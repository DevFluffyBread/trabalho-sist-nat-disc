const exprInput = document.getElementById('expr');
const errorBox  = document.getElementById('error');
const varGrid   = document.getElementById('varGrid');
const truthHead = document.querySelector('#truthTable thead tr');
const truthBody = document.querySelector('#truthTable tbody');
const analysisBox = document.getElementById('analysisBox');

"ABCDEFGHIJKLMNOPQRSTUVWXYZ".split('').slice(0,12).forEach(ch=>{
  const b = document.createElement('button');
  b.className='btn';
  b.textContent=ch;
  b.dataset.insert=ch;
  varGrid.appendChild(b);
});

document.querySelectorAll('[data-insert]').forEach(btn=>{
  btn.addEventListener('click',()=>{
    insertAtCursor(exprInput, btn.dataset.insert);
  });
});
document.getElementById('btnClear').addEventListener('click',()=>{
  exprInput.value='';
  truthHead.innerHTML=''; truthBody.innerHTML='';
  analysisBox.innerHTML='';
  errorBox.textContent='';
});
document.getElementById('btnGenerate').addEventListener('click', run);

function insertAtCursor(el, text){
  const {selectionStart:s, selectionEnd:e, value:v} = el;
  el.value = v.slice(0,s)+text+v.slice(e);
  const pos = s + text.length;
  el.focus(); el.setSelectionRange(pos,pos);
}

const ALLOWED = new Set(['∼','^','v','→','↔','(',')']);
function normalize(raw){
  let s = raw.replace(/\s+/g,'');
  s = s
    .replace(/¬|~/g,'∼')
    .replace(/∧/g,'^')
    .replace(/∨/g,'v')
    .replace(/<->|↔/g,'↔')
    .replace(/->|→/g,'→');
  s = s.replace(/v/g, '§OR§');
  s = s.toUpperCase();
  s = s.replace(/§OR§/g, 'v');
  return s;
}

function tokenize(s){
  const tokens=[];
  for(let i=0;i<s.length;i++){
    const c = s[i];
    if (ALLOWED.has(c)) { tokens.push(c); continue; }
    if (c>='A' && c<='Z'){ tokens.push({type:'VAR', value:c}); continue; }
    tokens.push({type:'INVALID', value:c});
  }
  return tokens;
}

function checkAllowedSymbols(tokens){
  for(const t of tokens){
    if (typeof t==='string'){
      if (!ALLOWED.has(t)) return `Símbolo inválido: "${t}"`;
    }else{
      if (t.type==='INVALID') return `Símbolo inválido: "${t.value}"`;
      if (t.type!=='VAR') return `Token inválido: ${JSON.stringify(t)}`;
    }
  }
  return null;
}

function parse(tokens){
  let i=0;
  const peek = () => tokens[i];
  const match = (val) => (tokens[i]===val ? (i++, true) : false);
  const isVar = (t)=> typeof t==='object' && t.type==='VAR';

  function A(){
    if (match('∼')) return {type:'not', sub:A()};
    if (isVar(peek())){ const v=tokens[i].value; i++; return {type:'var', name:v}; }
    if (match('(')){ const f=E(); if(!match(')')) throw new Error("Parêntese ')' esperado"); return f; }
    throw new Error('FBF inválida perto de "'+displayToken(peek())+'"');
  }
  function B(){
    let node=A();
    while (match('^')) node={type:'and', left:node, right:A()};
    return node;
  }
  function C(){
    let node=B();
    while (match('v')) node={type:'or', left:node, right:B()};
    return node;
  }
  function D(){
    let node=C();
    while (match('→')) node={type:'imp', left:node, right:C()};
    return node;
  }
  function E(){
    let node=D();
    while (match('↔')) node={type:'iff', left:node, right:D()};
    return node;
  }
  const ast = E();
  if (i !== tokens.length) throw new Error("Sobrou coisa após a FBF: '"+displayToken(tokens[i])+"'");
  return ast;
}
function displayToken(t){
  if (t==null) return 'fim';
  if (typeof t==='string') return t;
  if (t.type==='VAR') return t.value;
  return t.value ?? '?';
}

function collectVars(ast, set=new Set()){
  switch(ast.type){
    case 'var': set.add(ast.name); break;
    case 'not': collectVars(ast.sub,set); break;
    default: collectVars(ast.left,set); collectVars(ast.right,set);
  }
  return [...set].sort();
}

function evalAST(ast, env){
  switch(ast.type){
    case 'var': return !!env[ast.name];
    case 'not': return !evalAST(ast.sub, env);
    case 'and': return evalAST(ast.left, env) && evalAST(ast.right, env);
    case 'or' : return evalAST(ast.left, env) || evalAST(ast.right, env);
    case 'imp': return !evalAST(ast.left, env) || evalAST(ast.right, env);
    case 'iff': return evalAST(ast.left, env) === evalAST(ast.right, env);
  }
}

function isLiteral(sf){
  return sf.node.type==='var' || (sf.node.type==='not' && sf.node.sub.type==='var');
}

function decompose(sf){
  const s = sf.sign, n = sf.node;
  switch(n.type){
    case 'not':
      return { kind:'alpha', sets:[ [{sign:(s==='T'?'F':'T'), node:n.sub}] ] };
    case 'and':
      if (s==='T')  return {kind:'alpha', sets:[ [{sign:'T',node:n.left},{sign:'T',node:n.right}] ]};
      else          return {kind:'beta',  sets:[ [{sign:'F',node:n.left}], [{sign:'F',node:n.right}] ]};
    case 'or':
      if (s==='T')  return {kind:'beta',  sets:[ [{sign:'T',node:n.left}], [{sign:'T',node:n.right}] ]};
      else          return {kind:'alpha', sets:[ [{sign:'F',node:n.left},{sign:'F',node:n.right}] ]};
    case 'imp':
      if (s==='T')  return {kind:'beta',  sets:[ [{sign:'F',node:n.left}], [{sign:'T',node:n.right}] ]};
      else          return {kind:'alpha', sets:[ [{sign:'T',node:n.left},{sign:'F',node:n.right}] ]};
    case 'iff':
      if (s==='T')  return {kind:'beta',  sets:[
        [{sign:'T',node:n.left},{sign:'T',node:n.right}],
        [{sign:'F',node:n.left},{sign:'F',node:n.right}]
      ]};
      else          return {kind:'beta',  sets:[
        [{sign:'T',node:n.left},{sign:'F',node:n.right}],
        [{sign:'F',node:n.left},{sign:'T',node:n.right}]
      ]};
    case 'var':
      return null;
  }
}

function tableauClosed(initialSigned){
  const stack = [ { pending:[initialSigned], T:new Set(), F:new Set() } ];

  while(stack.length){
    const br = stack.pop();
    for(const v of br.T){ if (br.F.has(v)) { br.closed=true; break; } }
    if (br.closed) continue;

    const idx = br.pending.findIndex(sf => !isLiteral(sf));
    if (idx === -1){
      for(const sf of br.pending){
        if (sf.node.type==='var'){
          const v=sf.node.name;
          (sf.sign==='T' ? br.T : br.F).add(v);
        } else {
          const v=sf.node.sub.name;
          (sf.sign==='T' ? br.F : br.T).add(v);
        }
      }
      for(const v of br.T){ if (br.F.has(v)) { br.closed=true; break; } }
      if (!br.closed) return false;
      continue;
    }

    const sf = br.pending.splice(idx,1)[0];
    const rule = decompose(sf);
    if (!rule){ br.pending.push(sf); continue; }
    if (rule.kind==='alpha'){
      const child = cloneBranch(br);
      child.pending.push(...rule.sets[0]);
      stack.push(child);
    } else {
      for(const set of rule.sets){
        const child = cloneBranch(br);
        child.pending.push(...set);
        stack.push(child);
      }
    }
  }
  return true;
}

function cloneBranch(b){ return { pending:[...b.pending], T:new Set(b.T), F:new Set(b.F) } }

function run(){
  errorBox.textContent='';
  truthHead.innerHTML=''; truthBody.innerHTML='';
  analysisBox.innerHTML='';

  try{
    const normalized = normalize(exprInput.value);
    if (!normalized) throw new Error('Digite uma expressão.');
    const tokens = tokenize(normalized);
    const symErr = checkAllowedSymbols(tokens);
    if (symErr) throw new Error(symErr);

    const ast = parse(tokens);
    const vars = collectVars(ast);

    if (vars.length > 8){
      truthHead.innerHTML = `<th>Expressão</th>`;
      truthBody.innerHTML = `<tr><td style="text-align:left;padding:12px">Muitas variáveis (${vars.length}). A tabela ficaria enorme. O veredito abaixo (Tableaux) continua válido.</td></tr>`;
    }else{
      renderTruthTable(ast, vars);
    }

    const isFTClosed = tableauClosed({sign:'F', node:ast});
    const isTTClosed = tableauClosed({sign:'T', node:ast});
    const verdict = { taut: isFTClosed, contrad: isTTClosed, cont: !(isFTClosed || isTTClosed) };
    renderAnalysis(verdict);
  }catch(e){
    errorBox.textContent = e.message || String(e);
  }
}

function renderTruthTable(ast, vars){
  truthHead.innerHTML = vars.map(v=>`<th>${v}</th>`).join('') + `<th>${prettyExpr(normalize(exprInput.value))}</th>`;
  truthBody.innerHTML = '';

  const n = vars.length;
  const total = 1<<n;
  for(let mask=0; mask<total; mask++){
    const env={};
    for(let j=0;j<n;j++) env[vars[j]] = !!(mask & (1<<(n-j-1)));
    const val = evalAST(ast, env);

    const tr = document.createElement('tr');
    vars.forEach(v=>{
      const td=document.createElement('td');
      td.innerHTML = `<span class="badge ${env[v]?'v':'f'}">${env[v]?'V':'F'}</span>`;
      tr.appendChild(td);
    });
    const td=document.createElement('td');
    td.innerHTML = `<span class="badge ${val?'v':'f'}">${val?'V':'F'}</span>`;
    tr.appendChild(td);
    truthBody.appendChild(tr);
  }
}

function prettyExpr(s){ return s; }

function renderAnalysis(r){
  analysisBox.innerHTML='';
  let msg = '';
  if (r.taut) msg = 'Essa expressão é tautológica';
  else if (r.contrad) msg = 'Essa expressão é uma contradição';
  else msg = 'Essa expressão é contingente';

  const div=document.createElement('div');
  div.className='chip';
  const b=document.createElement('b');
  b.textContent = msg;
  div.appendChild(b);
  analysisBox.appendChild(div);
}

run();
