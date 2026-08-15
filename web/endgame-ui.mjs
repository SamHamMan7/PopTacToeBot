const nativeQuerySelector=document.querySelector.bind(document);
const computerOptions=nativeQuerySelector('#computerOptions');
let computerRules=null;
if(computerOptions&&!nativeQuerySelector('#computerRules')){
  const rulesLabel=document.createElement('label');
  rulesLabel.innerHTML='Computer rules<select id="computerRules"><option value="torus" selected>Solver torus — WebAssembly</option><option value="beginner">Beginner — Reincarnation</option></select>';
  const difficultyLabel=nativeQuerySelector('#difficulty')?.closest('label');
  if(difficultyLabel)computerOptions.insertBefore(rulesLabel,difficultyLabel);else computerOptions.prepend(rulesLabel);
  computerRules=rulesLabel.querySelector('#computerRules');
}else computerRules=nativeQuerySelector('#computerRules');

document.querySelector=function(selector){
  if(selector==='input[name="edge"][value="torus"]'&&computerRules?.value==='beginner'&&nativeQuerySelector('input[name="mode"][value="computer"]:checked')){
    return nativeQuerySelector('input[name="edge"][value="reincarnation"]');
  }
  return nativeQuerySelector(selector);
};

const link=document.createElement('link');link.rel='stylesheet';link.href='endgame-ui.css';document.head.append(link);
const difficulty=nativeQuerySelector('#difficulty');
function updateComputerEngineCopy(){
  const beginner=computerRules?.value==='beginner';
  if(difficulty){
    const strong=difficulty.querySelector('option[value="strong"]');
    if(strong)strong.textContent=beginner?'Strong — JavaScript':'Strong — WebAssembly';
    let maximum=difficulty.querySelector('option[value="maximum"]');
    if(!maximum){difficulty.insertAdjacentHTML('beforeend','<option value="maximum">Maximum — WebAssembly</option>');maximum=difficulty.querySelector('option[value="maximum"]')}
    if(maximum)maximum.textContent=beginner?'Maximum — JavaScript':'Maximum — WebAssembly';
  }
  const note=nativeQuerySelector('#computerOptions .warning-note');
  if(note)note.textContent=beginner
    ?'Beginner computer mode uses Reincarnation + Continue + Move When All on Board + King. All difficulties use the generic JavaScript search because the WebAssembly engine is Torus-only.'
    :'Strong and Maximum use the WebAssembly bitboard engine on Torus + Continue + Move When All on Board + King. JavaScript remains as an automatic fallback.';
}
updateComputerEngineCopy();
if(computerRules)computerRules.addEventListener('change',()=>{updateComputerEngineCopy();nativeQuerySelector('#restartButton')?.click()});
const think=nativeQuerySelector('#thinkTime');if(think)think.max='15';
const overlay=document.createElement('div');overlay.id='endgameOverlay';overlay.className='endgame-overlay';overlay.hidden=true;overlay.setAttribute('role','dialog');overlay.setAttribute('aria-modal','true');overlay.innerHTML='<div class="endgame-card"><p class="endgame-kicker">Game over</p><h2 id="endgameTitle">GAME OVER</h2><p id="endgameDetail" class="endgame-detail"></p><div class="endgame-actions"><button id="endgameRestart" class="button button-primary" type="button">Play again</button><button id="endgameUndo" class="button" type="button">Undo</button></div><button id="endgameDismiss" class="endgame-dismiss" type="button">View final board</button></div>';document.body.append(overlay);
const board=nativeQuerySelector('#board'),winner=nativeQuerySelector('#winner'),status=nativeQuerySelector('#gameStatus'),title=nativeQuerySelector('#endgameTitle'),detail=nativeQuerySelector('#endgameDetail');const dirs=[[0,1],[1,0],[1,1],[1,-1]];
function edge(){return nativeQuerySelector('input[name="edge"]:checked')?.value??'reincarnation'}function adv(c,e){let r=c.r+c.dr,k=c.c+c.dc;if(r>=0&&r<8&&k>=0&&k<8)return{...c,r,c:k};if(e==='torus')return{...c,r:(r+8)%8,c:(k+8)%8};return null}function color(i){const c=board?.children[i];return c?.querySelector('.checker.blue')?'blue':c?.querySelector('.checker.red')?'red':null}function clear(){for(const c of board?.children??[])c.classList.remove('winning-line','winning-blue','winning-red')}
function show(){if(!winner)return;const v=winner.textContent?.trim();if(!v||v==='—'){overlay.hidden=true;clear();return}clear();const e=edge();for(let s=0;s<64;s++){const col=color(s);if(!col)continue;for(const [dr,dc] of dirs){let cur={r:Math.floor(s/8),c:s%8,dr,dc},cells=[s],ok=true;for(let n=1;n<3;n++){cur=adv(cur,e);if(!cur){ok=false;break}const i=cur.r*8+cur.c;if(color(i)!==col){ok=false;break}cells.push(i)}if(ok&&(v==='Draw'||v.toLowerCase()===col))for(const i of cells)board.children[i].classList.add('winning-line',col==='blue'?'winning-blue':'winning-red')}}overlay.className='endgame-overlay '+(v==='Blue'?'blue':v==='Red'?'red':'draw');title.textContent=v==='Draw'?'DRAW':`${v.toUpperCase()} WINS`;detail.textContent=status?.textContent?.trim()||'Game over.';overlay.hidden=false}
nativeQuerySelector('#endgameRestart').addEventListener('click',()=>nativeQuerySelector('#restartButton')?.click());nativeQuerySelector('#endgameUndo').addEventListener('click',()=>nativeQuerySelector('#undoButton')?.click());nativeQuerySelector('#endgameDismiss').addEventListener('click',()=>overlay.hidden=true);if(winner)new MutationObserver(show).observe(winner,{childList:true,subtree:true,characterData:true});show();
