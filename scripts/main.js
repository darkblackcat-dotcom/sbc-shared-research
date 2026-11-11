(function(){

const CT = Packages.mindustry.ctype.ContentType;
const TechTree = Packages.mindustry.content.TechTree;
const Table = Packages.arc.scene.ui.layout.Table;
const srImageButton = Packages.arc.scene.ui.ImageButton;
const srAlign = Packages.arc.util.Align;
const srTex = Packages.mindustry.gen.Tex;
const srIcon = Packages.mindustry.gen.Icon;
const srColor = Packages.arc.graphics.Color;
const srTouchable = Packages.arc.scene.event.Touchable;
const srStyles = Packages.mindustry.ui.Styles;
const srMouseLeft = Packages.arc.input.KeyCode.mouseLeft;
const srItemSeq = Packages.mindustry.type.ItemSeq;

let registered = false;
let warmed = false;
let availQueued = false; // хост: рассылка списка уже запланирована на следующий кадр

// хост: минимальная пауза между запросами одного игрока
const MIN_DELAY = 100; // мс
const reqAt = {};       // id игрока -> время последнего sr_request
const helloAt = {};     // id игрока -> время последней обработки sr_hello
const helloDue = {};    // id игрока -> {player, at}: отложенный sr_hello
let availIds = {};
let treeOf = {};      // хост: id игрока -> корень открытого у него дерева
let sentTree = null;  // клиент: дерево, о котором последний раз сообщили хосту
let availList = null; // клиент: [{id, name, cost}] - что хост разрешил исследовать

let infoTbl = null;   // карточка узла
let infoBtn = null;   // кнопка узла, для которого открыта карточка
let infoGrace = 0;    // первые кадры после создания карточки не проверяем "мышь ушла"
let wasShown = false;
let pressBtn = null, pressX = 0, pressY = 0, wasDown = false; // ПК: отслеживание клика по узлу
const attached = new java.util.WeakHashMap(); // кнопки, на которые уже повешены обработчики

function tr(key, def){ return Core.bundle.get(key, def); }
function idOf(c){ return c.getContentType().name() + ":" + c.name; }

function jcall(c, name){
    const v = c[name];
    if(typeof v == "function") return c[name]();
    try{
        const f = c[name + "()"];
        if(typeof f == "function") return c[name + "()"]();
    }catch(e){}
    return v;
}
function isUnlocked(c){ return !!jcall(c, "unlocked"); }
function isUnlockedHost(c){ return !!jcall(c, "unlockedHost"); }

function findContent(id){
    id = String(id);
    const i = id.indexOf(":");
    if(i < 1) return null;
    try{ return Vars.content.getByName(CT.valueOf(id.substring(0, i)), id.substring(i + 1)); }
    catch(e){ return null; }
}

function rootName(n){ return n.name != null ? String(n.name) : idOf(n.content); }

function findRoot(name){
    if(name == null || String(name).length == 0) return null;
    name = String(name);
    for(let i = 0; i < TechTree.roots.size; i++){
        const r = TechTree.roots.get(i);
        if(rootName(r) == name) return r;
    }
    return null;
}

function defaultRoot(){
    try{
        const sec = Vars.state.rules.sector;
        if(sec != null && sec.planet != null) return sec.planet.techTree;
    }catch(e){}
    return null;
}

function treeNodes(root){
    const out = [];
    if(root == null) root = defaultRoot();
    if(root == null){
        const all = TechTree.all;
        for(let i = 0; i < all.size; i++) out.push(all.get(i));
        return out;
    }
    (function walk(n){
        out.push(n);
        for(let i = 0; i < n.children.size; i++) walk(n.children.get(i));
    })(root);
    return out;
}

function findNode(c, root){
    const all = treeNodes(root);
    for(let i = 0; i < all.length; i++){
        if(all[i].content == c) return all[i];
    }
    return null;
}

function realAmount(st){
    const v = Number(st.amount);
    return isNaN(v) ? 0 : Math.max(0, Math.round(v));
}

function costData(n, pool){
    const rq = n.requirements;
    const out = [];
    for(let i = 0; i < rq.length; i++){
        let fin = 0;
        try{ fin = Math.round(Number(n.finishedRequirements[i].amount)); }catch(e){}
        let have = -1;
        try{ if(pool != null) have = Math.round(Number(pool.get(rq[i].item))); }catch(e){}
        out.push(rq[i].item.name + "," + fin + "," + realAmount(rq[i]) + "," + have);
    }
    return out.length > 0 ? out.join("|") : "-";
}

function objectivesDone(n){
    try{
        const o = n.objectives;
        for(let i = 0; i < o.size; i++){
            if(!o.get(i).complete()) return false;
        }
    }catch(e){}
    return true;
}

function makePool(root){
    const planets = [];
    Vars.content.planets().each(p => {
        if(root != null && (p.techTree == root || root.planet == p)) planets.push(p);
    });
    if(planets.length == 0) planets.push(Packages.mindustry.content.Planets.serpulo);

    const cache = [];
    planets.forEach(pl => {
        pl.sectors.each(sec => {
            if(sec.hasBase() && !sec.isFrozen()) cache.push({sector: sec, seq: sec.items()});
        });
    });

    let cur = null;
    try{ cur = Vars.state.isCampaign() ? Vars.state.rules.sector : null; }catch(e){}

    if(cur != null && planets.indexOf(cur.planet) >= 0){
        const has = cache.some(e => e.sector == cur);
        if(!has){
            try{
                if(cur.isBeingPlayed()) cache.push({sector: cur, seq: cur.items()});
            }catch(e){}
        }
    }

    const pool = {};
    pool.get = function(item){
        let t = 0;
        cache.forEach(e => { t += Math.max(e.seq.get(item), 0); });
        return t;
    };
    pool.remove = function(item, amount){
        if(amount <= 0) return;
        let curAmount = 0;
        cache.forEach(e => { if(cur != null && e.sector == cur) curAmount = e.seq.get(item); });
        const percentage = amount / Math.max(pool.get(item) - curAmount, 1);
        const left = {v: amount};
        function take(e, limit){
            const toRemove = Math.min(left.v, limit);
            if(toRemove <= 0) return;
            if(e.pending == null) e.pending = new srItemSeq();
            e.pending.add(item, -toRemove);
            e.seq.remove(item, toRemove);
            left.v -= toRemove;
        }
        cache.forEach(e => {
            if(left.v == 0 || e.sector == cur) return;
            const available = e.seq.get(item);
            if(available <= 0) return;
            take(e, Math.min(Math.ceil(percentage * available), available));
        });
        if(left.v > 0 && cur != null){
            cache.forEach(e => {
                if(e.sector == cur) take(e, e.seq.get(item));
            });
        }
    };
    pool.commit = function(){
        cache.forEach(e => {
            if(e.pending == null) return;
            const seq = e.pending;
            e.pending = null;
            e.sector.addItems(seq);
        });
    };
    return pool;
}

function spend(n, root){
    const rq = n.requirements;
    const pool = makePool(root);
    let used = 0, complete = true;
    try{
        for(let i = 0; i < rq.length; i++){
            const need = realAmount(rq[i]);
            const fin = n.finishedRequirements[i];
            const left = Math.max(need - Math.round(Number(fin.amount)), 0);
            const take = Math.max(Math.min(left, pool.get(rq[i].item)), 0);
            if(take > 0){
                pool.remove(rq[i].item, take);
                fin.amount = Math.round(Number(fin.amount)) + take;
                used += take;
            }
            if(Math.round(Number(fin.amount)) < need) complete = false;
        }
    }finally{
        pool.commit();
    }
    try{ n.save(); }catch(e){}
    return {used: used, complete: complete};
}

function refreshHostItems(){
    try{
        if(Vars.headless || Vars.ui == null) return;
        if(Vars.ui.research.isShown()) Vars.ui.research.rebuildItems();
    }catch(e){}
}

function researchable(n){
    const c = n.content;
    if(c == null) return false;
    const t = c.getContentType();
    if(t != CT.block && t != CT.unit) return false;
    if(isUnlocked(c)) return false;
    if(n.parent != null && !isUnlocked(n.parent.content)) return false;
    return objectivesDone(n);
}

function hostResearch(id, rootNm){
    if(!Vars.state.isCampaign()) return "err:campaign";
    const c = findContent(id);
    if(c == null) return "err:notfound";
    const root = findRoot(rootNm) || defaultRoot();
    const n = findNode(c, root);
    if(n == null) return "err:notfound";
    const t = c.getContentType();
    if(t != CT.block && t != CT.unit) return "err:notfound";
    if(isUnlocked(c)) return "err:already";
    if(n.parent != null && !isUnlocked(n.parent.content)) return "err:parent";
    if(!objectivesDone(n)) return "err:objectives";
    const sp = spend(n, root);
    if(sp.used > 0) refreshHostItems();
    if(!sp.complete){
        if(sp.used == 0){
            return "err:resources";
        }
        return "part:" + c.localizedName;
    }

    c.unlock();
    try{ Events.fire(new EventType.ResearchEvent(c)); }catch(e){}
    return "ok:" + c.localizedName;
}

function buildAvail(rootNm){
    const root = findRoot(rootNm);
    const all = treeNodes(root);
    let pool = null;
    try{ pool = makePool(root || defaultRoot()); }catch(e){}
    const seen = {};
    const msgs = [];
    let chunk = "";
    let count = 0;
    function flush(){
        msgs.push((msgs.length == 0 ? "0|" : "1|") + chunk);
        chunk = "";
    }
    for(let i = 0; i < all.length; i++){
        const n = all[i];
        if(!researchable(n)) continue;
        if(seen[idOf(n.content)]) continue;
        seen[idOf(n.content)] = true;
        count++;
        const e = idOf(n.content) + "\t" + n.content.localizedName + "\t" + costData(n, pool);
        if(chunk.length + e.length + 1 > 3000) flush();
        chunk += (chunk.length > 0 ? "\n" : "") + e;
    }
    if(chunk.length > 0 || msgs.length == 0) flush();
    return {msgs: msgs, count: count};
}

function sendMsgs(con, msgs){
    msgs.forEach(m => Call.clientPacketReliable(con, "sr_avail", m));
}

function sendAvail(con, rootNm){
    const r = buildAvail(rootNm);
    sendMsgs(con, r.msgs);
}

function warmUp(){
    if(warmed) return;
    warmed = true;
    try{
        TechTree.roots.each(r => { buildAvail(rootName(r)); });
        buildAvail("");
    }catch(e){}
}

function sendAvailAll(){
    if(availQueued) return;
    availQueued = true;
    Core.app.post(() => {
        availQueued = false;
        const byTree = {};
        Groups.player.each(pl => {
            if(pl.con == null) return;
            const tree = treeOf[pl.id] || "";
            if(!byTree[tree]) byTree[tree] = [];
            byTree[tree].push(pl);
        });
        Object.keys(byTree).forEach(tree => {
            try{
                const r = buildAvail(tree);
                byTree[tree].forEach(pl => sendMsgs(pl.con, r.msgs));
            }catch(e){}
        });
    });
}

function showResult(s){
    s = String(s);
    if(s.indexOf("ok:") == 0 || s.indexOf("part:") == 0 || s == "err:resources") return;
    Vars.ui.showInfoToast(tr("sr." + s.replace(":", "."), s), 3);
}

function viewOf(){ return Vars.ui.research.view; }

function clientTreeName(){
    try{
        const n = Vars.ui.research.lastNode;
        if(n != null) return rootName(n);
    }catch(e){}
    return "";
}

function sendHello(){
    if(!Vars.net.client()) return;
    sentTree = clientTreeName();
    Call.serverPacketReliable("sr_hello", sentTree);
}

function entryOf(c){
    let found = null;
    if(availList != null) availList.forEach(e => { if(e.id == idOf(c)) found = e; });
    return found;
}

function requestNode(node){
    Call.serverPacketReliable("sr_request", clientTreeName() + "\t" + idOf(node.content));
}

function parseCost(str){
    const res = [];
    String(str).split("|").forEach(line => {
        const p = String(line).split(",");
        if(p.length < 4) return;
        const item = Vars.content.getByName(CT.item, p[0]);
        if(item == null) return;
        res.push({item: item, fin: parseInt(p[1]), need: parseInt(p[2]), have: parseInt(p[3])});
    });
    return res;
}

function clientCost(node){
    const res = [];
    const rq = node.requirements;
    for(let i = 0; i < rq.length; i++) res.push({item: rq[i].item, fin: 0, need: realAmount(rq[i]), have: -1});
    return res;
}

function fmt(v){
    try{ return String(Packages.mindustry.core.UI.formatAmount(v)); }catch(e){ return String(v); }
}

function progressPct(lines){
    let any = false, sum = 0, used = 0;
    lines.forEach(l => {
        const w = Number(l.item.cost);
        sum += w * l.need;
        used += w * l.fin;
        if(l.fin > 0) any = true;
    });
    if(!any || sum <= 0) return -1;
    return Math.min(Math.floor(used / sum * 100), 99);
}

function researchStyle(){
    try{
        const st = new Packages.arc.scene.ui.TextButton$TextButtonStyle();
        st.disabled = srTex.button;
        st.font = Packages.mindustry.ui.Fonts.def;
        st.fontColor = srColor.white;
        st.disabledFontColor = srColor.gray;
        st.up = srTex.buttonOver;
        st.over = srTex.buttonDown;
        return st;
    }catch(e){ return null; }
}

function hideInfo(){
    if(infoTbl != null){ try{ infoTbl.remove(); }catch(e){} }
    infoTbl = null;
    infoBtn = null;
}

function showInfo(btn){
    try{ showInfoImpl(btn); }
    catch(e){ hideInfo(); }
}

function showInfoImpl(btn){
    hideInfo();
    const v = viewOf();
    v.infoTable.remove();

    const node = btn.userObject;
    const c = node.content;
    const done = isUnlockedHost(c);
    const ent = done ? null : entryOf(c);
    const selectable = done || objectivesDone(node);

    const t = new Table();
    t.left();
    t.background(srTex.button).margin(8);

    const head = new Table();
    head.left();
    head.margin(0).left();
    head.defaults().left();

    const body = new Table();
    body.left();
    body.defaults().left();
    body.add(selectable ? c.localizedName : "[accent]???").left().row();

    if(done){
        body.add("@completed").left().row();
    }else if(!selectable){
        body.add("@complete").left().row();
        node.objectives.each(o => {
            if(!o.complete()) body.add("> " + o.display()).color(srColor.lightGray).left().row();
        });
    }else{
        const lines = ent != null ? parseCost(ent.cost) : clientCost(node);
        const pct = progressPct(lines);
        if(pct >= 0){
            const hasVanilla = String(Core.bundle.get("research.progress", "")).length > 0;
            const txt = Core.bundle.format(hasVanilla ? "research.progress" : "sr.progress", pct);
            body.add(txt).color(srColor.lightGray).left().row();
        }
        lines.forEach(l => {
            const rest = l.need - l.fin;
            if(rest <= 0) return;
            const row = new Table();
            row.left();
            row.image(l.item.uiIcon).size(8 * 3).padRight(3);
            row.add(l.item.localizedName).color(srColor.lightGray);
            const amt = l.have < 0 ? fmt(rest) : fmt(Math.min(l.have, rest)) + " / " + fmt(rest);
            row.add(" " + amt).color(l.have == 0 ? srColor.scarlet : srColor.lightGray);
            body.add(row).fillX().left().row();
        });
    }

    if(selectable){
        head.button(srIcon.info, srStyles.flati, () => {
            try{ Vars.ui.content.show(c); }catch(e){}
        }).growY().width(50);
    }
    head.add(new Table()).grow();
    head.add(body).pad(9).left().growX();

    if(!done && Vars.mobile){
        head.row();
        const can = ent != null;
        const label = tr("research", tr("sr.request", "Request research"));
        const st = researchStyle();
        const cell = st != null
            ? head.button(label, srIcon.ok, st, () => requestNode(node))
            : head.button(label, srIcon.ok, () => requestNode(node));
        cell.disabled(b => !can).growX().height(44).colspan(3);
    }
    t.add(head).growX().left();
    t.row();

    try{
        if(selectable && c.description != null && c.inlineDescription){
            const d = c.displayDescription();
            const dt = new Table();
            dt.margin(3).left();
            dt.labelWrap(d).color(srColor.lightGray).maxWidth(String(d).length > 20 ? 270 : 0).growX();
            t.add(dt).fillX();
        }
    }catch(e){}

    t.update(() => {
        if(infoGrace > 0){ infoGrace--; t.pack(); }
        else if(!Vars.mobile && !isOverCard(btn, t)){ hideInfo(); return; }
        const right = btn.x + btn.getWidth() + t.getWidth();
        if(right > Core.graphics.getWidth()) t.setPosition(btn.x, btn.y + btn.getHeight(), srAlign.topRight);
        else t.setPosition(btn.x + btn.getWidth(), btn.y + btn.getHeight(), srAlign.topLeft);
    });
    t.touchable = srTouchable.enabled;
    t.pack();
    v.addChild(t);
    t.pack();
    infoTbl = t;
    infoBtn = btn;
    infoGrace = 5;
    if(!Vars.mobile) v.hoverNode = btn;
}

function isWithin(el, root){
    while(el != null){
        if(el == root) return true;
        el = el.parent;
    }
    return false;
}

function isOverCard(btn, t){
    const e = Core.scene.hit(Core.input.mouseX(), Core.input.mouseY(), true);
    return isWithin(e, btn) || isWithin(e, t);
}

function refreshInfo(){
    if(infoBtn != null) showInfo(infoBtn);
}

function isTechNodeButton(el){
    if(!(el instanceof srImageButton)) return false;
    const ud = el.userObject;
    return ud != null && String(ud.getClass().getSimpleName()) == "TechNode";
}

function nodeUnderMouse(){
    const v = viewOf();
    let e = Core.scene.hit(Core.input.mouseX(), Core.input.mouseY(), true);
    while(e != null && e != v){
        if(isTechNodeButton(e)) return e;
        e = e.parent;
    }
    return null;
}

function pollClick(){
    const down = Core.input.keyDown(srMouseLeft);
    if(down && !wasDown){
        pressBtn = nodeUnderMouse();
        pressX = Core.input.mouseX();
        pressY = Core.input.mouseY();
    }else if(!down && wasDown && pressBtn != null){
        const b = pressBtn;
        pressBtn = null;
        const moved = Math.abs(Core.input.mouseX() - pressX) + Math.abs(Core.input.mouseY() - pressY);
        if(moved < 12 && nodeUnderMouse() == b){
            const node = b.userObject;
            const c = node.content;
            if(!isUnlockedHost(c) && entryOf(c) != null) requestNode(node);
        }
    }
    wasDown = down;
}

function hookNode(btn){
    if(Vars.mobile){
        btn.clicked(() => {
            if(!Vars.net.client() || viewOf().moved) return;
            showInfo(btn);
        });
    }else{
        btn.hovered(() => {
            if(Vars.net.client() && btn != infoBtn) showInfo(btn);
        });
    }
}

function attachNodes(){
    viewOf().getChildren().each(el => {
        if(attached.containsKey(el) || !isTechNodeButton(el)) return;
        attached.put(el, true);
        hookNode(el);
    });
}

function nowMs(){ return java.lang.System.currentTimeMillis(); }

function onHello(player, tree){
    const same = treeOf[player.id] === tree;
    treeOf[player.id] = tree;
    const t = nowMs();
    const last = helloAt[player.id] || 0;
    if(t - last >= MIN_DELAY){
        helloAt[player.id] = t;
        delete helloDue[player.id];
        sendAvail(player.con, tree);
    }else if(!same && !helloDue[player.id]){ 
        helloDue[player.id] = {player: player, at: last + MIN_DELAY};
    }
}

function setup(){
    if(registered) return;
    registered = true;

    Vars.netServer.addPacketHandler("sr_request", (player, data) => {
        const p = String(data).split("\t");
        const tree = p.length > 1 ? String(p[0]) : (treeOf[player.id] || "");
        const id = p.length > 1 ? String(p[1]) : String(p[0]);
        const t = nowMs();
        if(t - (reqAt[player.id] || 0) < MIN_DELAY) return;
        reqAt[player.id] = t;
        treeOf[player.id] = tree;
        let r;
        try{ r = hostResearch(id, tree); }
        catch(e){ r = "err:internal"; }
        Call.clientPacketReliable(player.con, "sr_result", r);
        if(r.indexOf("part:") == 0) sendAvailAll();
        else if(r.indexOf("ok:") != 0) sendAvail(player.con, tree);
    });
    Vars.netServer.addPacketHandler("sr_hello", (player, tree) => {
        try{ onHello(player, String(tree)); }
        catch(e){}
    });

    Vars.netClient.addPacketHandler("sr_avail", s => {
        s = String(s);
        if(s.indexOf("0|") == 0 || availList == null){ availList = []; availIds = {}; }
        s.substring(2).split("\n").forEach(line => {
            if(line.length == 0) return;
            const p = String(line).split("\t");
            const id = String(p[0]);
            if(availIds[id]) return;
            availIds[id] = true;
            availList.push({id: id, name: p.length > 1 ? String(p[1]) : id, cost: p.length > 2 ? String(p[2]) : "-"});
        });
        refreshInfo();
    });
    Vars.netClient.addPacketHandler("sr_result", s => {
        showResult(s);
        refreshInfo();
    });

    warmUp();
}

Events.on(EventType.ClientLoadEvent, setup);
Events.on(EventType.ServerLoadEvent, setup);

Events.on(EventType.UnlockEvent, e => {
    if(Vars.net.server() && e.content != null) sendAvailAll();
    if(Vars.net.client()) Core.app.post(() => refreshInfo());
});

Events.on(EventType.PlayerLeave, e => {
    const id = e.player.id;
    delete treeOf[id];
    delete reqAt[id];
    delete helloAt[id];
    delete helloDue[id];
});

Events.run(EventType.Trigger.update, () => {
    if(!Vars.net.server()) return;
    Object.keys(helloDue).forEach(id => {
        const d = helloDue[id];
        if(nowMs() < d.at) return;
        delete helloDue[id];
        if(!d.player.isAdded() || d.player.con == null) return;
        helloAt[id] = nowMs();
        try{ sendAvail(d.player.con, treeOf[id]); }
        catch(e){}
    });
});

Events.on(EventType.WorldLoadEvent, () => {
    if(Vars.net.client()){
        availList = null;
        sentTree = null;
        sendHello();
    }
});

Events.run(EventType.Trigger.update, () => {
    if(!Vars.net.client() || !registered) return;
    const cur = clientTreeName();
    let helloSent = false; // hello уже отправлен в этом кадре
    if(sentTree !== null && cur !== sentTree){
        availList = null;
        hideInfo();
        sendHello();
        helloSent = true;
    }

    let shown = false;
    try{ shown = Vars.ui.research.isShown(); }catch(e){}
    if(!shown){
        wasShown = false;
        pressBtn = null;
        if(infoTbl != null) hideInfo();
        return;
    }
    if(!wasShown){
        wasShown = true;
        if(!helloSent) sendHello();
    }

    try{
        const v = viewOf();
        if(v.infoTable.hasParent()) v.infoTable.remove();
        v.hoverNode = Vars.mobile ? null : infoBtn;

        attachNodes();

        if(Vars.mobile){
            if(infoTbl != null && Core.input.justTouched()){
                const hit = Core.scene.hit(Core.input.mouseX(), Core.input.mouseY(), true);
                if(hit == v) hideInfo();
            }
        }else{
            pollClick();
        }
    }catch(e){}
});

})();
