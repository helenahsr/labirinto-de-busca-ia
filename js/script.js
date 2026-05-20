// ==========================================================================
// LABIRINTO HEURÍSTICO — Implementação comentada
// ==========================================================================
// Este arquivo implementa um visualizador de busca informada em labirintos.
// O fluxo geral é:
//   1. Gerar um labirinto aleatório (recursive backtracking)
//   2. Posicionar o rato (início fixo em [0,0]) e o queijo (aleatório)
//   3. Executar um algoritmo de busca: A* ou Busca Gulosa Best-First
//   4. Animar em três fases: exploração → caminho ótimo → movimento do rato
// ==========================================================================

// Atalho para document.getElementById — evita repetição ao longo do código
const $ = (id) => document.getElementById(id);

// ─────────────────────────────────────────────────────────────────────────────
// ESTADO GLOBAL
// Um único objeto centraliza todos os dados da aplicação. Isso evita variáveis
// soltas e facilita o acesso em qualquer função.
// ─────────────────────────────────────────────────────────────────────────────
const state = {
  grid: [],        // Matriz 2-D: 0 = célula aberta, 1 = parede
  size: 21,        // Dimensão do labirinto (sempre ímpar para o algoritmo funcionar)
  start: [0, 0],   // Coordenada [x, y] do ponto de partida do rato
  cheese: [0, 0],  // Coordenada [x, y] do queijo (objetivo)
  cells: [],       // Matriz 2-D de elementos <div> do DOM (espelha o grid)
  running: false,  // Flag que impede múltiplas execuções simultâneas
  speed: 3,        // Nível de velocidade da animação (1 = lento … 5 = veloz)
  algorithm: 'astar', // Algoritmo selecionado: 'astar' | 'greedy'
  mousePos: [0, 0],   // Posição atual do ícone do rato no DOM
  abortController: null, // Reservado para cancelamento futuro de animações
};

// ─────────────────────────────────────────────────────────────────────────────
// UTILITÁRIOS
// ─────────────────────────────────────────────────────────────────────────────

// Pausa a execução por `ms` milissegundos. Usado nas animações assíncronas.
const sleep = (ms) => new Promise(r => setTimeout(r, ms));

// Converte coordenadas (x, y) numa string única "x,y".
// Funciona como chave em Map/Set, já que arrays não são comparados por valor em JS.
const key = (x, y) => `${x},${y}`;

// Fisher-Yates: embaralha um array in-place e o retorna.
// Usado para randomizar a ordem de exploração de vizinhos na geração do labirinto.
const shuffle = (arr) => {
  for (let i = arr.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [arr[i], arr[j]] = [arr[j], arr[i]];
  }
  return arr;
};

// Distância de Manhattan: soma das diferenças absolutas de coordenadas.
// É uma heurística ADMISSÍVEL para grids ortogonais — nunca superestima o custo real,
// pois cada passo custa 1 e não há movimento diagonal.
const manhattan = (a, b) => Math.abs(a[0] - b[0]) + Math.abs(a[1] - b[1]);


// ─────────────────────────────────────────────────────────────────────────────
// GERAÇÃO DO LABIRINTO — Recursive Backtracking (versão iterativa com pilha)
// ─────────────────────────────────────────────────────────────────────────────
// Algoritmo:
//   - Inicia com tudo bloqueado (grid = 1)
//   - A partir de uma célula, "escava" em direção aleatória pulando 2 células
//     (isso garante que sempre há uma parede entre dois caminhos adjacentes)
//   - Se não há onde escavar, volta pela pilha (backtracking)
//
// Resultado: labirinto PERFEITO — conexo, sem ciclos, com exatamente um
// caminho entre quaisquer dois pontos. Isso garante que o rato sempre pode
// chegar ao queijo.
// ─────────────────────────────────────────────────────────────────────────────
function generateMaze(size) {
  // Começa com todas as células bloqueadas
  const grid = Array.from({ length: size }, () => Array(size).fill(1));

  const stack = [[0, 0]]; // Pilha de células a explorar (começa em [0,0])
  grid[0][0] = 0;         // Abre a célula inicial

  while (stack.length > 0) {
    const [x, y] = stack[stack.length - 1]; // Célula atual (topo da pilha)

    // Direções possíveis — pula 2 posições para sempre aterrissar em células,
    // não em paredes intermediárias
    const dirs = shuffle([[0, -2], [0, 2], [-2, 0], [2, 0]]);
    let carved = false;

    for (const [dx, dy] of dirs) {
      const nx = x + dx, ny = y + dy;

      // Verifica se o vizinho está dentro dos limites e ainda é parede
      if (nx >= 0 && nx < size && ny >= 0 && ny < size && grid[ny][nx] === 1) {
        grid[ny][nx] = 0;                   // Abre a célula destino
        grid[y + dy / 2][x + dx / 2] = 0;  // Abre a parede intermediária (o "corredor")
        stack.push([nx, ny]);               // Avança para a nova célula
        carved = true;
        break; // Processa apenas uma direção por iteração (profundidade primeiro)
      }
    }

    // Se não encontrou nenhum vizinho válido, retrocede
    if (!carved) stack.pop();
  }
  return grid;
}

// Escolhe uma posição para o queijo: célula aberta cuja distância de Manhattan
// à origem seja pelo menos size/2 — assim o queijo fica relativamente longe do rato.
// Se não existir candidato suficientemente distante, aceita qualquer célula aberta.
function placeCheese(grid, start) {
  const size = grid.length;
  const candidates = [];

  for (let y = 0; y < size; y++) {
    for (let x = 0; x < size; x++) {
      if (grid[y][x] === 0 && manhattan([x, y], start) >= size / 2) {
        candidates.push([x, y]);
      }
    }
  }

  // Fallback: qualquer célula aberta que não seja a origem
  if (candidates.length === 0) {
    for (let y = 0; y < size; y++) {
      for (let x = 0; x < size; x++) {
        if (grid[y][x] === 0 && (x !== start[0] || y !== start[1])) candidates.push([x, y]);
      }
    }
  }

  return candidates[Math.floor(Math.random() * candidates.length)];
}


// ─────────────────────────────────────────────────────────────────────────────
// ALGORITMO DE BUSCA — A* e Busca Gulosa Best-First
// ─────────────────────────────────────────────────────────────────────────────
// Ambos os algoritmos compartilham a mesma estrutura. A diferença está em f(n):
//
//   A*:     f(n) = g(n) + h(n)   →  custo real acumulado + estimativa até o objetivo
//   Gulosa: f(n) = h(n)          →  só a estimativa; ignora o caminho já percorrido
//
// A* garante o caminho ÓTIMO (menor custo total).
// A Busca Gulosa é geralmente mais rápida, mas pode retornar caminhos subótimos.
//
// Retorna { path, exploreOrder } para que a animação possa reproduzir o processo.
// ─────────────────────────────────────────────────────────────────────────────
function search(grid, start, goal, algorithm) {
  const size = grid.length;

  // Função heurística: distância de Manhattan de (x,y) até o objetivo
  const h = (x, y) => manhattan([x, y], goal);

  const open = new Map();    // Fronteira: nós candidatos a expandir  { key → {x,y,f,g} }
  const closed = new Set();  // Nós já expandidos (não revisitados)
  const cameFrom = new Map();// Registro de "quem gerou quem" — usado para reconstruir o caminho
  const gScore = new Map();  // Custo real g(n) para cada nó visitado
  const exploreOrder = [];   // Ordem em que os nós foram expandidos (para animação)

  // Inicializa com o nó de início
  const startKey = key(...start);
  gScore.set(startKey, 0);
  open.set(startKey, { x: start[0], y: start[1], g: 0, f: h(...start) });

  while (open.size > 0) {
    // Seleciona o nó com menor f na fronteira (O(n) — aceitável para labirintos pequenos)
    let bestKey = null;
    let best = null;
    for (const [k, node] of open) {
      if (!best || node.f < best.f) { best = node; bestKey = k; }
    }

    open.delete(bestKey);    // Remove da fronteira
    closed.add(bestKey);     // Marca como expandido
    exploreOrder.push([best.x, best.y]); // Registra para animação

    // Chegamos ao objetivo — reconstrói o caminho de trás para frente
    if (best.x === goal[0] && best.y === goal[1]) {
      const path = [];
      let cur = bestKey;
      while (cur) {
        const [x, y] = cur.split(',').map(Number);
        path.unshift([x, y]); // Insere no início para obter ordem correta
        cur = cameFrom.get(cur);
      }
      return { path, exploreOrder };
    }

    // Expande os 4 vizinhos ortogonais (cima, baixo, esquerda, direita)
    for (const [dx, dy] of [[0, 1], [0, -1], [1, 0], [-1, 0]]) {
      const nx = best.x + dx, ny = best.y + dy;

      // Ignora células fora dos limites, paredes ou já expandidas
      if (nx < 0 || nx >= size || ny < 0 || ny >= size) continue;
      if (grid[ny][nx] === 1) continue;
      const nKey = key(nx, ny);
      if (closed.has(nKey)) continue;

      // Custo g do vizinho = custo atual + 1 (cada passo tem custo uniforme)
      const tentativeG = best.g + 1;

      // Atualiza apenas se encontrarmos um caminho mais barato até este vizinho
      if (!gScore.has(nKey) || tentativeG < gScore.get(nKey)) {
        cameFrom.set(nKey, bestKey);   // Registra o pai
        gScore.set(nKey, tentativeG);
        const hVal = h(nx, ny);

        // DIFERENÇA ENTRE OS ALGORITMOS:
        // A*:     considera custo real + estimativa
        // Gulosa: considera apenas a estimativa
        const fVal = algorithm === 'astar' ? tentativeG + hVal : hVal;

        open.set(nKey, { x: nx, y: ny, g: tentativeG, f: fVal });
      }
    }
  }

  // Fronteira esgotada sem encontrar o objetivo (não deveria ocorrer em labirintos perfeitos)
  return { path: null, exploreOrder };
}


// ─────────────────────────────────────────────────────────────────────────────
// RENDERIZAÇÃO — Constrói o DOM a partir do estado atual
// ─────────────────────────────────────────────────────────────────────────────
// Cria um <div class="cell"> para cada posição do grid, aplica as classes
// corretas (wall, start, cheese) e insere os ícones emoji.
// Também popula `state.cells` para acesso rápido nas animações.
function render() {
  const grid = $('mazeGrid');
  grid.innerHTML = ''; // Limpa o labirinto anterior

  // Define o CSS Grid com o número exato de colunas e linhas
  grid.style.gridTemplateColumns = `repeat(${state.size}, 1fr)`;
  grid.style.gridTemplateRows    = `repeat(${state.size}, 1fr)`;
  state.cells = [];

  for (let y = 0; y < state.size; y++) {
    const row = [];
    for (let x = 0; x < state.size; x++) {
      const cell = document.createElement('div');
      cell.className = 'cell';

      if (state.grid[y][x] === 1) cell.classList.add('wall');  // Célula bloqueada

      // Marca a célula de início
      if (x === state.start[0]  && y === state.start[1])  cell.classList.add('start');

      // Marca a célula do queijo e insere o ícone
      if (x === state.cheese[0] && y === state.cheese[1]) {
        cell.classList.add('cheese');
        const icon = document.createElement('span');
        icon.className = 'icon cheese-icon';
        icon.textContent = '🧀';
        cell.appendChild(icon);
      }

      grid.appendChild(cell);
      row.push(cell);
    }
    state.cells.push(row);
  }

  // Posiciona o rato na célula de partida e sincroniza o estado
  placeMouseDOM(state.start[0], state.start[1]);
  state.mousePos = [...state.start];

  // Atualiza o label de dimensão no painel informativo
  $('infoGrid').textContent = `${state.size}×${state.size}`;
}

// Move o ícone do rato no DOM para a posição (x, y).
// Remove o ícone da célula anterior antes de inserir na nova.
function placeMouseDOM(x, y) {
  // Remove classe e ícone do rato de qualquer célula que os tenha
  document.querySelectorAll('.cell.mouse-here').forEach(c => {
    c.classList.remove('mouse-here');
    const mi = c.querySelector('.icon.mouse-icon');
    if (mi) mi.remove();
  });

  const cell = state.cells[y][x];
  cell.classList.add('mouse-here');

  // Insere o ícone apenas se ainda não existir (evita duplicatas)
  if (!cell.querySelector('.icon.mouse-icon')) {
    const icon = document.createElement('span');
    icon.className = 'icon mouse-icon';
    icon.textContent = '🐭';
    cell.appendChild(icon);
  }
}

// Remove todas as classes de visualização (explored, frontier, path, trail)
// e reposiciona o rato na largada — útil antes de uma nova busca.
function clearSearchOverlay() {
  for (let y = 0; y < state.size; y++) {
    for (let x = 0; x < state.size; x++) {
      const cell = state.cells[y][x];
      cell.classList.remove('explored', 'frontier', 'path', 'trail');
    }
  }
  placeMouseDOM(state.start[0], state.start[1]);
  state.mousePos = [...state.start];
}


// ─────────────────────────────────────────────────────────────────────────────
// ANIMAÇÃO — Três fases sequenciais
// ─────────────────────────────────────────────────────────────────────────────
// A função é assíncrona: usa `await sleep()` para criar pausas visuais entre
// frames sem bloquear o navegador. `state.running` atua como flag de cancelamento.
//
// Fase 1 — Exploração: pinta as células na ordem em que foram visitadas pelo algoritmo
// Fase 2 — Caminho:    destaca o caminho ótimo encontrado
// Fase 3 — Movimento:  anima o rato percorrendo o caminho célula a célula
// ─────────────────────────────────────────────────────────────────────────────
async function animate(result) {
  const { path, exploreOrder } = result;

  // Mapeamento de nível de velocidade → delay em milissegundos por frame
  const speeds = { 1: 35, 2: 18, 3: 10, 4: 5, 5: 2 };
  const baseDelay = speeds[state.speed];

  setStatus('running', 'Explorando...');

  // ── FASE 1: Exploração ──────────────────────────────────────────────────
  for (let i = 0; i < exploreOrder.length; i++) {
    if (!state.running) return; // Aborta se o usuário parou a execução

    const [x, y] = exploreOrder[i];
    const cell = state.cells[y][x];

    // Não sobrescreve as classes visuais da célula de início e do queijo
    if (!cell.classList.contains('start') && !cell.classList.contains('cheese')) {
      cell.classList.add('explored');
    }

    // Atualiza o contador de nós explorados em tempo real
    $('statExplored').textContent = i + 1;

    // Agrupa frames em velocidades altas para evitar sobrecarga do DOM
    if (baseDelay >= 5 || i % 3 === 0) {
      await sleep(baseDelay);
    }
  }

  // Sem caminho: informa o usuário e encerra
  if (!path) {
    setStatus('error', 'Sem caminho');
    showToast('Nenhum caminho encontrado.', true);
    return;
  }

  // ── FASE 2: Destaque do caminho ótimo ───────────────────────────────────
  await sleep(200); // Pequena pausa entre fases para clareza visual
  setStatus('running', 'Traçando caminho...');

  for (let i = 0; i < path.length; i++) {
    if (!state.running) return;
    const [x, y] = path[i];
    const cell = state.cells[y][x];

    if (!cell.classList.contains('start') && !cell.classList.contains('cheese')) {
      cell.classList.remove('explored'); // Remove a cor de "explorado"
      cell.classList.add('path');        // Aplica a cor do caminho ótimo
    }
    await sleep(Math.max(15, baseDelay * 2)); // Delay um pouco maior para visibilidade
  }

  // ── FASE 3: Movimento do rato ────────────────────────────────────────────
  await sleep(300);
  setStatus('running', 'Rato em movimento...');

  for (let i = 0; i < path.length; i++) {
    if (!state.running) return;
    const [x, y] = path[i];

    // A célula anterior vira "trilha" (rastro deixado pelo rato)
    if (i > 0) {
      const [px, py] = path[i - 1];
      const prev = state.cells[py][px];
      if (!prev.classList.contains('start') && !prev.classList.contains('cheese')) {
        prev.classList.remove('path');
        prev.classList.add('trail');
      }
    }

    placeMouseDOM(x, y);        // Move o ícone do rato para a célula atual
    state.mousePos = [x, y];    // Atualiza o estado lógico
    await sleep(Math.max(60, baseDelay * 5)); // Passo mais lento para dramatismo
  }

  setStatus('done', 'Queijo capturado!');
  showToast('🎉 Queijo encontrado!');
}


// ─────────────────────────────────────────────────────────────────────────────
// HELPERS DE UI
// ─────────────────────────────────────────────────────────────────────────────

// Atualiza o indicador de status no cabeçalho do painel do labirinto.
// `kind` define a cor do ponto: 'running' | 'done' | 'error' | '' (neutro)
function setStatus(kind, text) {
  const dot = $('statusDot');
  dot.classList.remove('running', 'done', 'error'); // Limpa estado anterior
  if (kind) dot.classList.add(kind);
  $('statusText').textContent = text;
}

// Exibe uma mensagem flutuante (toast) na tela por ~2,4 segundos.
// `isError` aplica estilo de erro (cor diferente).
let toastTimer; // Armazena o timer para cancelar um toast anterior se necessário
function showToast(msg, isError = false) {
  const t = $('toast');
  t.textContent = msg;
  t.classList.toggle('error', isError);
  t.classList.add('show');
  clearTimeout(toastTimer);
  toastTimer = setTimeout(() => t.classList.remove('show'), 2400);
}


// ─────────────────────────────────────────────────────────────────────────────
// FLUXO PRINCIPAL
// ─────────────────────────────────────────────────────────────────────────────

// Lê o slider de tamanho, gera um novo labirinto e renderiza tudo do zero.
// O slider vai de 5 a 20 (lógico); o tamanho real é sempre ímpar: size = logical*2 + 1
// (necessário para o algoritmo de backtracking funcionar corretamente).
function generateAndRender() {
  const logical = parseInt($('sizeInput').value);
  state.size   = logical * 2 + 1; // Converte para tamanho real ímpar (11, 13, …, 41)
  state.grid   = generateMaze(state.size);
  state.cheese = placeCheese(state.grid, state.start);
  render();
  resetStats();
  setStatus('', 'Pronto');
}

// Mantém o labirinto atual mas sorteia uma nova posição para o queijo.
function regenerateCheese() {
  state.cheese = placeCheese(state.grid, state.start);
  render();
  resetStats();
  setStatus('', 'Queijo reposicionado');
}

// Reseta os displays de métricas para o estado inicial (—).
function resetStats() {
  $('statPath').textContent     = '—';
  $('statExplored').textContent = '—';
  $('statTime').textContent     = '—';
  $('statEff').textContent      = '—';
}

// Orquestra a busca completa:
//   1. Impede execução dupla
//   2. Executa o algoritmo sincronamente (rápido) e mede o tempo
//   3. Exibe as métricas
//   4. Inicia a animação assíncrona
async function runSearch() {
  if (state.running) return; // Guarda de re-entrada

  clearSearchOverlay();
  resetStats();
  state.running = true;

  // Desabilita os botões durante a execução para evitar estados inconsistentes
  $('btnRun').disabled        = true;
  $('btnGenerate').disabled   = true;
  $('btnMoveCheese').disabled = true;

  // O algoritmo de busca roda de forma síncrona (sem animação) — é muito rápido
  const t0 = performance.now();
  const result = search(state.grid, state.start, state.cheese, state.algorithm);
  const t1 = performance.now();

  // Preenche as métricas no painel lateral
  if (result.path) {
    $('statPath').textContent     = result.path.length - 1; // -1 pois a origem não é "passo"
    $('statExplored').textContent = result.exploreOrder.length;
    $('statTime').textContent     = (t1 - t0).toFixed(1);
    // Eficiência: razão entre comprimento do caminho e total de nós explorados
    // 100% = o algoritmo não explorou nenhum nó além do caminho ótimo
    const eff = ((result.path.length / result.exploreOrder.length) * 100).toFixed(0);
    $('statEff').textContent = eff;
  } else {
    $('statExplored').textContent = result.exploreOrder.length;
    $('statTime').textContent     = (t1 - t0).toFixed(1);
  }

  // Agora inicia a animação visual (assíncrona)
  await animate(result);

  // Reabilita tudo ao final
  state.running = false;
  $('btnRun').disabled        = false;
  $('btnGenerate').disabled   = false;
  $('btnMoveCheese').disabled = false;
}


// ─────────────────────────────────────────────────────────────────────────────
// EVENTOS — Ligam os elementos do HTML às funções da aplicação
// ─────────────────────────────────────────────────────────────────────────────

// Botão "Gerar Novo Labirinto"
$('btnGenerate').addEventListener('click', () => {
  if (state.running) return;
  generateAndRender();
});

// Botão "Reposicionar Queijo"
$('btnMoveCheese').addEventListener('click', () => {
  if (state.running) return;
  regenerateCheese();
});

// Botão "Limpar Visualização" — remove cores de busca sem gerar novo labirinto
$('btnReset').addEventListener('click', () => {
  if (state.running) return;
  clearSearchOverlay();
  resetStats();
  setStatus('', 'Pronto');
});

// Botão "Executar Busca"
$('btnRun').addEventListener('click', runSearch);

// Slider de tamanho — atualiza o label em tempo real enquanto arrasta
$('sizeInput').addEventListener('input', (e) => {
  const logical = parseInt(e.target.value);
  const real = logical * 2 + 1;
  $('sizeValue').textContent = `${real} × ${real}`;
});

// Quando o usuário solta o slider de tamanho, gera um novo labirinto
$('sizeInput').addEventListener('change', () => {
  if (state.running) return;
  generateAndRender();
});

// Slider de velocidade — atualiza o estado e o label descritivo
$('speedInput').addEventListener('input', (e) => {
  state.speed = parseInt(e.target.value);
  const labels = { 1: 'Lenta', 2: 'Calma', 3: 'Média', 4: 'Rápida', 5: 'Veloz' };
  $('speedValue').textContent = labels[state.speed];
});

// Radio buttons de algoritmo — atualiza o estado e o label de info
document.querySelectorAll('input[name="algo"]').forEach(input => {
  input.addEventListener('change', (e) => {
    state.algorithm = e.target.value;
    $('infoAlgo').textContent = e.target.value === 'astar' ? 'A*' : 'Gulosa';
  });
});

// Atalhos de teclado para agilizar a interação:
//   Espaço → Executar busca
//   R      → Gerar novo labirinto
//   C      → Reposicionar queijo
document.addEventListener('keydown', (e) => {
  if (e.target.tagName === 'INPUT') return; // Ignora se o foco estiver num input
  if (e.code === 'Space') { e.preventDefault(); runSearch(); }
  if (e.key === 'r' || e.key === 'R') generateAndRender();
  if (e.key === 'c' || e.key === 'C') regenerateCheese();
});


// ─────────────────────────────────────────────────────────────────────────────
// INICIALIZAÇÃO
// Executa assim que o script é carregado, gerando o primeiro labirinto.
// ─────────────────────────────────────────────────────────────────────────────
generateAndRender();