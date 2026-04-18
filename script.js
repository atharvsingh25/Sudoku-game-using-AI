/* ═══════════════════════════════════════════════════════
   SUDOKU — DAA Project  |  script.js
   Algorithms: Backtracking, Constraint Propagation, AC-3
   ═══════════════════════════════════════════════════════ */

"use strict";

// ════════════════════════════════════════════════════════
// SECTION 1 — CONSTANTS & CONFIGURATION
// ════════════════════════════════════════════════════════

/** Number of cells to REMOVE per difficulty level */
const DIFFICULTY_CLUES = {
  easy:   30,   // remove 30 → 51 givens
  medium: 40,   // remove 40 → 41 givens
  hard:   50,   // remove 50 → 31 givens
  expert: 58    // remove 58 → 23 givens
};

// ════════════════════════════════════════════════════════
// SECTION 2 — GAME STATE
// ════════════════════════════════════════════════════════

let puzzle         = [];   // 9×9 — original puzzle (0 = empty)
let solution       = [];   // 9×9 — completed solution
let userGrid       = [];   // 9×9 — user's current entries
let notes          = [];   // 9×9 — each cell is a Set of candidate digits
let selected       = null; // { row, col } or null
let mistakes       = 0;
let hintsLeft      = 3;
let hintsUsed      = 0;
let notesMode      = false;
let history        = [];   // undo stack
let timerInterval  = null;
let seconds        = 0;
let gameActive     = false;
let totalEmpty     = 0;    // empty cells at game start
let currentDifficulty = 'medium';

// ════════════════════════════════════════════════════════
// SECTION 3 — UTILITY HELPERS
// ════════════════════════════════════════════════════════

/**
 * Returns a randomly shuffled copy of [1..9].
 * Used so generated puzzles are not identical each time.
 */
function shuffledNums() {
  const n = [1, 2, 3, 4, 5, 6, 7, 8, 9];
  for (let i = n.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [n[i], n[j]] = [n[j], n[i]];
  }
  return n;
}

/**
 * Deep-copies a 9×9 array.
 */
function copyGrid(grid) {
  return grid.map(row => [...row]);
}

// ════════════════════════════════════════════════════════
// SECTION 4 — CONSTRAINT CHECKING  (Core DAA Logic)
// ════════════════════════════════════════════════════════

/**
 * isValid — Constraint Propagation check.
 * Returns true if placing `num` at (row, col) in `grid`
 * does NOT violate Sudoku rules (row / column / 3×3 box).
 *
 * Time complexity per call: O(27) = O(1) for a 9×9 grid.
 */
function isValid(grid, row, col, num) {
  // ── Row constraint ──────────────────────────────────
  if (grid[row].includes(num)) return false;

  // ── Column constraint ────────────────────────────────
  for (let r = 0; r < 9; r++) {
    if (grid[r][col] === num) return false;
  }

  // ── 3×3 Box constraint ───────────────────────────────
  const boxRow = Math.floor(row / 3) * 3;
  const boxCol = Math.floor(col / 3) * 3;
  for (let r = boxRow; r < boxRow + 3; r++) {
    for (let c = boxCol; c < boxCol + 3; c++) {
      if (grid[r][c] === num) return false;
    }
  }

  return true;
}

/**
 * findEmpty — returns [row, col] of the first empty cell,
 * or null if no empty cell exists.
 * Used by both the generator and the solver.
 */
function findEmpty(grid) {
  for (let r = 0; r < 9; r++) {
    for (let c = 0; c < 9; c++) {
      if (grid[r][c] === 0) return [r, c];
    }
  }
  return null;
}

// ════════════════════════════════════════════════════════
// SECTION 5 — BACKTRACKING SOLVER  (Core DAA Logic)
// ════════════════════════════════════════════════════════

/**
 * solveSudoku — Backtracking algorithm.
 *
 * Algorithm:
 *   1. Find next empty cell.  If none → puzzle is solved → return true.
 *   2. Try digits 1–9 in order.
 *   3. If digit is valid (constraint check), place it and recurse.
 *   4. If recursion returns false → BACKTRACK (undo placement).
 *   5. If no digit works → return false (trigger backtrack in caller).
 *
 * Time  complexity: O(9^(n²)) worst-case  (n = grid size = 9)
 * Space complexity: O(n²) due to recursion call stack depth
 */
function solveSudoku(grid) {
  const empty = findEmpty(grid);
  if (!empty) return true;           // ← base case: solved!

  const [row, col] = empty;

  for (let num = 1; num <= 9; num++) {
    if (isValid(grid, row, col, num)) {
      grid[row][col] = num;          // ← tentative placement

      if (solveSudoku(grid)) return true;  // ← recurse

      grid[row][col] = 0;            // ← BACKTRACK
    }
  }

  return false;                      // ← trigger backtrack
}

/**
 * countSolutions — used during puzzle generation to ensure
 * the puzzle has EXACTLY ONE solution (uniqueness guarantee).
 *
 * We cap at `limit` (default 2) so we stop early if we
 * already know there are multiple solutions.
 */
function countSolutions(grid, limit = 2) {
  const empty = findEmpty(grid);
  if (!empty) return 1;

  const [r, c] = empty;
  let count = 0;

  for (let num = 1; num <= 9; num++) {
    if (isValid(grid, r, c, num)) {
      grid[r][c] = num;
      count += countSolutions(grid, limit);
      grid[r][c] = 0;
      if (count >= limit) return count;
    }
  }
  return count;
}

// ════════════════════════════════════════════════════════
// SECTION 6 — PUZZLE GENERATOR
// ════════════════════════════════════════════════════════

/**
 * fillGrid — fills an empty grid with a valid, randomised
 * complete Sudoku solution using backtracking + shuffled
 * digit order for variety.
 */
function fillGrid(grid) {
  const empty = findEmpty(grid);
  if (!empty) return true;

  const [r, c] = empty;

  for (const num of shuffledNums()) {       // ← shuffled for randomness
    if (isValid(grid, r, c, num)) {
      grid[r][c] = num;
      if (fillGrid(grid)) return true;
      grid[r][c] = 0;                       // ← backtrack
    }
  }
  return false;
}

/**
 * generatePuzzle — produces a valid Sudoku puzzle with a
 * UNIQUE solution for the requested difficulty.
 *
 * Steps:
 *   1. Generate a fully filled grid (solution).
 *   2. Shuffle cell order.
 *   3. Try removing each cell one by one.
 *   4. After each removal, verify exactly 1 solution remains.
 *   5. Stop when the target number of removals is reached.
 */
function generatePuzzle(difficulty) {
  // Step 1 — create complete solution
  const full = Array.from({ length: 9 }, () => Array(9).fill(0));
  fillGrid(full);
  solution = copyGrid(full);  // save solution globally

  const puz = copyGrid(full);

  // Step 2 — shuffle all cell positions
  const cells = [];
  for (let r = 0; r < 9; r++)
    for (let c = 0; c < 9; c++)
      cells.push([r, c]);

  for (let i = cells.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [cells[i], cells[j]] = [cells[j], cells[i]];
  }

  // Step 3–5 — remove cells while preserving uniqueness
  let removed = 0;
  const target = DIFFICULTY_CLUES[difficulty];

  for (const [r, c] of cells) {
    if (removed >= target) break;

    const backup = puz[r][c];
    puz[r][c] = 0;

    const test = copyGrid(puz);
    if (countSolutions(test) === 1) {
      removed++;
    } else {
      puz[r][c] = backup;   // restore — removal breaks uniqueness
    }
  }

  return puz;
}

// ════════════════════════════════════════════════════════
// SECTION 7 — DOM HELPERS
// ════════════════════════════════════════════════════════

/** Returns the <div class="cell"> for a given row/col */
function getCell(r, c) {
  return document.querySelector(`.cell[data-row="${r}"][data-col="${c}"]`);
}

/** Adds an entry to the move log panel */
function addLog(msg, type = '') {
  const log = document.getElementById('log');
  const entry = document.createElement('div');
  entry.className = 'log-entry' + (type ? ' ' + type : '');
  entry.textContent = msg;
  log.insertBefore(entry, log.firstChild);
  while (log.children.length > 30) log.removeChild(log.lastChild);
}

function clearLog() {
  document.getElementById('log').innerHTML = '';
}

/** Formats seconds as MM:SS */
function formatTime(s) {
  return String(Math.floor(s / 60)).padStart(2, '0') + ':' +
         String(s % 60).padStart(2, '0');
}

function updateTimer() {
  document.getElementById('timer').textContent = formatTime(seconds);
}

/** Updates the "X cells left" counter and progress bar */
function updateCellsLeft() {
  let left = 0;
  for (let r = 0; r < 9; r++)
    for (let c = 0; c < 9; c++)
      if (puzzle[r][c] === 0 && userGrid[r][c] === 0) left++;

  document.getElementById('cells-left').textContent = left;

  // Progress bar
  if (totalEmpty > 0) {
    const filled = totalEmpty - left;
    const pct = Math.round((filled / totalEmpty) * 100);
    document.getElementById('progress').style.width = pct + '%';
  }
}

/** Dims numpad buttons for digits that are fully placed (9 times) */
function updateNumpad() {
  const counts = Array(10).fill(0);
  for (let r = 0; r < 9; r++)
    for (let c = 0; c < 9; c++) {
      const v = puzzle[r][c] || userGrid[r][c];
      if (v) counts[v]++;
    }
  document.querySelectorAll('.num-btn').forEach(btn => {
    const n = parseInt(btn.dataset.num);
    btn.classList.toggle('disabled', counts[n] >= 9);
  });
}

// ════════════════════════════════════════════════════════
// SECTION 8 — BOARD RENDERING
// ════════════════════════════════════════════════════════

/** One-time: build all 81 cell <div>s inside #board */
function buildBoard() {
  const board = document.getElementById('board');
  board.innerHTML = '';
  for (let r = 0; r < 9; r++) {
    for (let c = 0; c < 9; c++) {
      const cell = document.createElement('div');
      cell.className = 'cell';
      cell.dataset.row = r;
      cell.dataset.col = c;
      cell.addEventListener('click', () => selectCell(r, c));
      board.appendChild(cell);
    }
  }
}

/** Renders the notes grid inside a cell */
function renderNotes(cell, r, c) {
  const div = document.createElement('div');
  div.className = 'notes';
  for (let n = 1; n <= 9; n++) {
    const span = document.createElement('span');
    span.className = 'note-digit' + (notes[r][c].has(n) ? '' : ' hidden');
    span.textContent = n;
    div.appendChild(span);
  }
  cell.appendChild(div);
}

/**
 * Full re-render of every cell to match current state.
 * Called after every state change.
 */
function renderBoard() {
  for (let r = 0; r < 9; r++) {
    for (let c = 0; c < 9; c++) {
      const cell = getCell(r, c);
      // Reset
      cell.className = 'cell';
      cell.dataset.row = r;
      cell.dataset.col = c;
      cell.innerHTML = '';

      if (puzzle[r][c] !== 0) {
        // Given (original) digit
        cell.textContent = puzzle[r][c];
        cell.classList.add('given');
      } else if (userGrid[r][c] !== 0) {
        // User-entered digit
        cell.textContent = userGrid[r][c];
        if (userGrid[r][c] !== solution[r][c]) {
          cell.classList.add('error');
        }
      } else if (notes[r][c].size > 0) {
        // Notes (pencil marks)
        renderNotes(cell, r, c);
      }
    }
  }

  // Re-apply selection highlighting
  if (selected) highlightSelected(selected.row, selected.col);

  updateCellsLeft();
}

/**
 * Highlights:
 *   - selected cell (blue outline)
 *   - same row / col / box (dim highlight)
 *   - cells with the same digit (light purple tint)
 */
function highlightSelected(r, c) {
  document.querySelectorAll('.cell').forEach(cell => {
    cell.classList.remove('selected', 'highlight', 'same-num');
  });

  const val = userGrid[r][c] || puzzle[r][c];

  for (let i = 0; i < 9; i++) {
    for (let j = 0; j < 9; j++) {
      const cell = getCell(i, j);
      if (i === r && j === c) {
        cell.classList.add('selected');
      } else if (
        i === r || j === c ||
        (Math.floor(i / 3) === Math.floor(r / 3) &&
         Math.floor(j / 3) === Math.floor(c / 3))
      ) {
        cell.classList.add('highlight');
      }
      // Same-digit highlight
      if (val !== 0 &&
          (userGrid[i][j] === val || puzzle[i][j] === val) &&
          !(i === r && j === c)) {
        cell.classList.add('same-num');
      }
    }
  }

  updateAlgoInfo(r, c);
}

// ════════════════════════════════════════════════════════
// SECTION 9 — ALGORITHM INFO PANEL
// ════════════════════════════════════════════════════════

/**
 * Shows constraint info for the selected cell in the
 * Algorithm panel on the right.
 */
function updateAlgoInfo(r, c) {
  // Merge puzzle givens + user entries for constraint check
  const merged = puzzle.map((row, ri) =>
    row.map((v, ci) => v || userGrid[ri][ci])
  );

  const validDigits = [];
  for (let n = 1; n <= 9; n++) {
    if (isValid(merged, r, c, n)) validDigits.push(n);
  }

  document.getElementById('algo-step').innerHTML =
    `Cell <span>R${r + 1} C${c + 1}</span><br>` +
    `Box <span>${Math.floor(r / 3) * 3 + Math.floor(c / 3) + 1}</span> | ` +
    `Row <span>${r + 1}</span> | Col <span>${c + 1}</span><br>` +
    `Valid digits: <span>${validDigits.join(', ') || 'none'}</span><br>` +
    `Domain size: <span>${validDigits.length}</span> value(s)<br>` +
    `Answer: <span>${puzzle[r][c] ? '(given)' : solution[r][c]}</span>`;
}

// ════════════════════════════════════════════════════════
// SECTION 10 — GAME CONTROL FUNCTIONS
// ════════════════════════════════════════════════════════

/** Starts a brand-new game */
function newGame() {
  document.getElementById('win-overlay').classList.remove('show');
  clearInterval(timerInterval);

  // Reset all state
  seconds        = 0;
  mistakes       = 0;
  hintsLeft      = 3;
  hintsUsed      = 0;
  history        = [];
  notesMode      = false;
  selected       = null;
  gameActive     = true;

  // Reset UI
  document.getElementById('mistakes').textContent   = '0 / 3';
  document.getElementById('hint-count').textContent = '0';
  document.getElementById('hint-btn').textContent   = '💡 Hint (3 left)';
  document.getElementById('hint-btn').disabled      = false;
  document.getElementById('notes-btn').classList.remove('active');
  document.getElementById('progress').style.width   = '0%';
  updateTimer();

  // Generate puzzle (may take ~200ms for Expert)
  puzzle   = generatePuzzle(currentDifficulty);
  userGrid = Array.from({ length: 9 }, () => Array(9).fill(0));
  notes    = Array.from({ length: 9 }, () =>
               Array.from({ length: 9 }, () => new Set()));

  totalEmpty = puzzle.flat().filter(v => v === 0).length;

  buildBoard();
  renderBoard();
  updateNumpad();
  clearLog();
  addLog('New ' + currentDifficulty + ' game started', 'hint');

  timerInterval = setInterval(() => {
    seconds++;
    updateTimer();
  }, 1000);
}

/** Selects a cell and triggers highlighting */
function selectCell(r, c) {
  if (!gameActive) return;
  selected = { row: r, col: c };
  highlightSelected(r, c);
}

/**
 * Places a digit in the selected cell (or toggles a note).
 * Validates against solution and tracks mistakes.
 */
function inputNumber(num) {
  if (!selected || !gameActive) return;
  const { row, col } = selected;
  if (puzzle[row][col] !== 0) return;   // can't edit given cells

  // ── Notes mode ───────────────────────────────────────
  if (notesMode) {
    history.push({
      type: 'note',
      row, col,
      notesCopy: new Set(notes[row][col])
    });
    if (notes[row][col].has(num)) notes[row][col].delete(num);
    else                          notes[row][col].add(num);
    renderBoard();
    return;
  }

  // ── Normal mode ──────────────────────────────────────
  history.push({
    type:      'input',
    row, col,
    prev:      userGrid[row][col],
    notesCopy: new Set(notes[row][col])
  });
  notes[row][col].clear();
  userGrid[row][col] = num;

  if (num !== 0 && num !== solution[row][col]) {
    // Wrong digit
    mistakes++;
    document.getElementById('mistakes').textContent = mistakes + ' / 3';
    addLog(`❌ R${row + 1}C${col + 1}: ${num} is wrong`, 'bad');
    if (mistakes >= 3) {
      addLog('💀 Too many mistakes! Game over.', 'bad');
      gameActive = false;
      clearInterval(timerInterval);
    }
  } else if (num !== 0) {
    // Correct digit — trigger pop-in animation
    setTimeout(() => {
      const cell = getCell(row, col);
      if (cell) cell.classList.add('solved-anim');
    }, 0);
    addLog(`✓ R${row + 1}C${col + 1}: ${num} placed correctly`, 'good');
  }

  renderBoard();
  updateNumpad();
  checkWin();
}

/** Erases the user's entry in the selected cell */
function erase() {
  if (!selected || !gameActive) return;
  const { row, col } = selected;
  if (puzzle[row][col] !== 0) return;

  history.push({
    type:      'input',
    row, col,
    prev:      userGrid[row][col],
    notesCopy: new Set(notes[row][col])
  });
  userGrid[row][col] = 0;
  notes[row][col].clear();
  renderBoard();
}

/** Undoes the last action */
function undo() {
  if (!history.length || !gameActive) return;
  const last = history.pop();
  if (last.type === 'input') {
    userGrid[last.row][last.col] = last.prev;
    notes[last.row][last.col]    = last.notesCopy;
  } else if (last.type === 'note') {
    notes[last.row][last.col] = last.notesCopy;
  }
  renderBoard();
  updateNumpad();
  addLog('↩ Undo', 'hint');
}

/** Gives a hint by revealing a random empty/wrong cell */
function giveHint() {
  if (!gameActive || hintsLeft <= 0) return;

  const candidates = [];
  for (let r = 0; r < 9; r++)
    for (let c = 0; c < 9; c++)
      if (puzzle[r][c] === 0 && userGrid[r][c] !== solution[r][c])
        candidates.push([r, c]);

  if (!candidates.length) return;

  const [r, c] = candidates[Math.floor(Math.random() * candidates.length)];

  history.push({
    type:      'input',
    row: r, col: c,
    prev:      userGrid[r][c],
    notesCopy: new Set(notes[r][c])
  });

  userGrid[r][c] = solution[r][c];
  notes[r][c].clear();

  hintsLeft--;
  hintsUsed++;
  document.getElementById('hint-count').textContent = hintsUsed;
  document.getElementById('hint-btn').textContent   = `💡 Hint (${hintsLeft} left)`;
  if (hintsLeft === 0) document.getElementById('hint-btn').disabled = true;

  selected = { row: r, col: c };
  renderBoard();
  updateNumpad();
  addLog(`💡 Hint: R${r + 1}C${c + 1} = ${solution[r][c]}`, 'hint');
  checkWin();
}

/** Highlights all incorrect user entries */
function checkBoard() {
  let allOk = true;
  for (let r = 0; r < 9; r++) {
    for (let c = 0; c < 9; c++) {
      if (puzzle[r][c] === 0 &&
          userGrid[r][c] !== 0 &&
          userGrid[r][c] !== solution[r][c]) {
        allOk = false;
        getCell(r, c).classList.add('error');
      }
    }
  }
  if (allOk) addLog('✅ All placed values are correct!', 'good');
  else        addLog('⚠️ Some values are incorrect', 'bad');
}

/** Resets user entries (keeps puzzle givens) */
function resetBoard() {
  if (!puzzle.length) return;

  userGrid   = Array.from({ length: 9 }, () => Array(9).fill(0));
  notes      = Array.from({ length: 9 }, () =>
                 Array.from({ length: 9 }, () => new Set()));
  history    = [];
  mistakes   = 0;
  hintsLeft  = 3;
  hintsUsed  = 0;
  gameActive = true;

  document.getElementById('mistakes').textContent   = '0 / 3';
  document.getElementById('hint-count').textContent = '0';
  document.getElementById('hint-btn').textContent   = '💡 Hint (3 left)';
  document.getElementById('hint-btn').disabled      = false;

  seconds = 0;
  clearInterval(timerInterval);
  timerInterval = setInterval(() => { seconds++; updateTimer(); }, 1000);

  renderBoard();
  updateNumpad();
  addLog('↺ Board reset', 'hint');
}

/**
 * Auto-solve with animated backtracking visualisation.
 *
 * Records every "place" and "backtrack" step, then
 * replays them at speed so the user can watch the
 * backtracking algorithm in action.
 */
function autoSolve() {
  if (!gameActive) return;
  gameActive = false;
  clearInterval(timerInterval);
  addLog('⚡ Auto-solving with Backtracking…', 'hint');

  // Build a work grid from current state
  const workGrid = userGrid.map((row, r) =>
    row.map((v, c) => puzzle[r][c] || v)
  );

  const steps = [];

  function solveStep(grid) {
    const empty = findEmpty(grid);
    if (!empty) return true;

    const [r, c] = empty;
    if (puzzle[r][c] !== 0) return solveStep(grid);   // skip givens

    for (let num = 1; num <= 9; num++) {
      if (isValid(grid, r, c, num)) {
        grid[r][c] = num;
        steps.push({ r, c, n: num });
        if (solveStep(grid)) return true;
        grid[r][c] = 0;
        steps.push({ r, c, n: 0 });
      }
    }
    return false;
  }

  solveStep(workGrid);

  // Animate the recorded steps
  const batchSize = currentDifficulty === 'expert' ? 5 : 10;
  let i = 0;

  const animate = setInterval(() => {
    for (let b = 0; b < batchSize; b++) {
      if (i >= steps.length) {
        clearInterval(animate);
        return;
      }
      const { r, c, n } = steps[i++];
      userGrid[r][c] = n;
    }
    renderBoard();
  }, 16);
}

/** Shows the win overlay if every cell is correctly filled */
function checkWin() {
  for (let r = 0; r < 9; r++)
    for (let c = 0; c < 9; c++)
      if (puzzle[r][c] === 0 && userGrid[r][c] !== solution[r][c])
        return;

  // All cells correct!
  gameActive = false;
  clearInterval(timerInterval);

  document.getElementById('win-time').textContent     = formatTime(seconds);
  document.getElementById('win-mistakes').textContent = mistakes;

  setTimeout(() => {
    document.getElementById('win-overlay').classList.add('show');
  }, 600);
}

/** Toggles notes (pencil) mode */
function toggleNotes() {
  notesMode = !notesMode;
  document.getElementById('notes-btn').classList.toggle('active', notesMode);
}

// ════════════════════════════════════════════════════════
// SECTION 11 — NUMPAD BUILD
// ════════════════════════════════════════════════════════

function buildNumpad() {
  const numpad = document.getElementById('numpad');
  numpad.innerHTML = '';
  for (let n = 1; n <= 9; n++) {
    const btn = document.createElement('button');
    btn.className   = 'num-btn';
    btn.textContent = n;
    btn.dataset.num = n;
    btn.addEventListener('click', () => inputNumber(n));
    numpad.appendChild(btn);
  }
}

// ════════════════════════════════════════════════════════
// SECTION 12 — KEYBOARD SUPPORT
// ════════════════════════════════════════════════════════

document.addEventListener('keydown', e => {
  if (!gameActive) return;

  // Digit input
  if (e.key >= '1' && e.key <= '9') {
    inputNumber(parseInt(e.key));
    return;
  }

  // Erase
  if (e.key === '0' || e.key === 'Backspace' || e.key === 'Delete') {
    erase();
    return;
  }

  // Undo
  if ((e.ctrlKey || e.metaKey) && e.key === 'z') {
    undo();
    return;
  }

  // Toggle notes
  if (e.key === 'n' || e.key === 'N') {
    toggleNotes();
    return;
  }

  // Arrow-key navigation
  if (!selected) return;
  const { row, col } = selected;
  const moves = {
    ArrowUp:    [-1,  0],
    ArrowDown:  [ 1,  0],
    ArrowLeft:  [ 0, -1],
    ArrowRight: [ 0,  1]
  };

  if (moves[e.key]) {
    e.preventDefault();
    const [dr, dc] = moves[e.key];
    selectCell(
      Math.max(0, Math.min(8, row + dr)),
      Math.max(0, Math.min(8, col + dc))
    );
  }
});

// ════════════════════════════════════════════════════════
// SECTION 13 — BUTTON EVENT LISTENERS
// ════════════════════════════════════════════════════════

document.getElementById('new-game-btn').addEventListener('click', newGame);
document.getElementById('solve-btn')   .addEventListener('click', autoSolve);
document.getElementById('hint-btn')    .addEventListener('click', giveHint);
document.getElementById('reset-btn')   .addEventListener('click', resetBoard);
document.getElementById('undo-btn')    .addEventListener('click', undo);
document.getElementById('erase-btn')   .addEventListener('click', erase);
document.getElementById('notes-btn')   .addEventListener('click', toggleNotes);
document.getElementById('check-btn')   .addEventListener('click', checkBoard);

// Difficulty selector
document.querySelectorAll('.diff-btn').forEach(btn => {
  btn.addEventListener('click', () => {
    document.querySelectorAll('.diff-btn').forEach(b => b.classList.remove('active'));
    btn.classList.add('active');
    currentDifficulty = btn.dataset.level;
  });
});

// ════════════════════════════════════════════════════════
// SECTION 14 — INITIALISE ON PAGE LOAD
// ════════════════════════════════════════════════════════

buildBoard();
buildNumpad();
newGame();