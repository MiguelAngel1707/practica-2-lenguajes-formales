"""Subset construction (Kozen 1997, Lecture 6).

Reads NFA cases from stdin (or from a file given as the first argument),
prints the table of the equivalent DFA for each case, and writes an
`output.html` file with the NFA/DFA diagrams and tables.

SI2002 Formal Languages - Assignment 2 - Universidad EAFIT.
"""

import html
import math
import sys
from collections import deque
from itertools import combinations

OUTPUT_HTML = "output.html"
# Above this many NFA states the power set (2^n rows) is too large to print,
# so only the reachable part of the DFA is listed.
FULL_TABLE_LIMIT = 12


# --------------------------------------------------------------------------
# Input parsing
# --------------------------------------------------------------------------

def tokenize(line):
    """Split a line into tokens, treating '{' and '}' as separate tokens."""
    return line.replace("{", " { ").replace("}", " } ").split()


def parse_set(tokens, pos):
    """Read one cell of the table: either `0` (the empty set) or `{ q ... }`.

    Returns the set and the position right after it.
    """
    if tokens[pos] == "{":
        pos += 1
        states = []
        while tokens[pos] != "}":
            states.append(int(tokens[pos]))
            pos += 1
        return frozenset(states), pos + 1
    if tokens[pos] == "0":
        return frozenset(), pos + 1
    raise ValueError("expected `0` or `{ ... }`, found %r" % tokens[pos])


def read_cases(text):
    """Parse the whole input into a list of NFAs.

    Each NFA is a dict with keys: n, alphabet, initial, final, delta.
    `delta` maps (state, symbol) -> frozenset of states.
    """
    lines = text.splitlines()
    idx = 0

    def next_line():
        nonlocal idx
        line = lines[idx]
        idx += 1
        return line

    case_count = int(next_line().split()[0])
    cases = []
    for _ in range(case_count):
        n = int(next_line().split()[0])
        initial = frozenset(int(t) for t in next_line().split())
        alphabet = next_line().split()
        final = frozenset(int(t) for t in next_line().split())

        delta = {}
        for _ in range(n):
            tokens = tokenize(next_line())
            state = int(tokens[0])
            pos = 1
            for symbol in alphabet:
                target, pos = parse_set(tokens, pos)
                delta[(state, symbol)] = target

        cases.append({
            "n": n,
            "alphabet": alphabet,
            "initial": initial,
            "final": final,
            "delta": delta,
        })
    return cases


# --------------------------------------------------------------------------
# Subset construction (Kozen, Lecture 6)
# --------------------------------------------------------------------------

def power_set(n):
    """All subsets of {1, ..., n}, ordered by size and then by elements."""
    states = list(range(1, n + 1))
    subsets = []
    for size in range(n + 1):
        for combo in combinations(states, size):
            subsets.append(frozenset(combo))
    return subsets


def subset_construction(nfa):
    """Build the DFA M = (2^Q, Sigma, delta, S, {A | A ∩ F != {}}) from N."""
    n, alphabet = nfa["n"], nfa["alphabet"]
    nfa_delta, final = nfa["delta"], nfa["final"]

    def step(subset, symbol):
        """delta(A, a) = union of Delta(q, a) for every q in A."""
        target = set()
        for state in subset:
            target |= nfa_delta[(state, symbol)]
        return frozenset(target)

    dfa_initial = nfa["initial"]

    # The full DFA: every subset of Q is a state.
    all_states = power_set(n)
    transitions = {}
    for subset in all_states:
        for symbol in alphabet:
            transitions[(subset, symbol)] = step(subset, symbol)
    dfa_final = [s for s in all_states if s & final]

    # Reachable part: only used for the diagrams, the construction itself
    # is unchanged.
    reachable = []
    seen = {dfa_initial}
    queue = deque([dfa_initial])
    while queue:
        subset = queue.popleft()
        reachable.append(subset)
        for symbol in alphabet:
            target = transitions[(subset, symbol)]
            if target not in seen:
                seen.add(target)
                queue.append(target)

    return {
        "alphabet": alphabet,
        "states": all_states,
        "transitions": transitions,
        "initial": dfa_initial,
        "final": dfa_final,
        "reachable": reachable,
    }


# --------------------------------------------------------------------------
# Naming and formatting helpers
# --------------------------------------------------------------------------

def set_to_text(subset):
    """Render a set of NFA states the way the assignment writes them."""
    if not subset:
        return "0"
    return "{" + " ".join(str(q) for q in sorted(subset)) + "}"


def name_states(states):
    """Rename the DFA states as A0, A1, ... (the assignment allows this)."""
    return {subset: "A%d" % i for i, subset in enumerate(states)}


def marker(subset, dfa):
    """`->` for the initial state, `<-` for final states, as in the PDF."""
    if subset == dfa["initial"]:
        return "->"
    if subset in dfa["final"]:
        return "<-"
    return "  "


def dfa_rows(dfa, names, states):
    """Build the printable rows of the DFA table."""
    rows = []
    for subset in states:
        cells = [names[dfa["transitions"][(subset, a)]] for a in dfa["alphabet"]]
        rows.append((marker(subset, dfa), names[subset], set_to_text(subset), cells))
    return rows


def print_dfa(dfa, names, states):
    """Print the DFA table to stdout, with no extra blank lines."""
    header = ["", "", "state"] + list(dfa["alphabet"])
    rows = [(m, name, subset, cells) for m, name, subset, cells in dfa_rows(dfa, names, states)]
    table = [header] + [[m, name, subset] + cells for m, name, subset, cells in rows]
    widths = [max(len(row[i]) for row in table) for i in range(len(header))]
    for row in table:
        print(" ".join(cell.ljust(widths[i]) for i, cell in enumerate(row)).rstrip())


# --------------------------------------------------------------------------
# Automaton diagrams: hand-drawn SVG (optional feature of the assignment)
#
# The diagrams are laid out here instead of with a diagramming library so that
# self-loops, back edges and pairs of opposite transitions never overlap, and
# so the drawing always fits inside its box.
# --------------------------------------------------------------------------

RADIUS = 27           # radius of a state
COL_W = 185           # horizontal distance between two columns
ROW_H = 114           # vertical distance between two states of a column
PAD_X = 78            # side margin (leaves room for the incoming start arrow)
PAD_TOP = 86          # top margin (leaves room for the self-loops)
PAD_BOTTOM = 62
TURN = 52             # where an arrow turns aside, in the gap between columns

CANDIDATE_OFFSETS = (0, 32, -32, 58, -58, 92, -92, 130, -130)

NODE_STYLE = {
    "plain": ("#e0e7ff", "#4338ca", "#1e1b4b"),
    "final": ("#bbf7d0", "#15803d", "#052e16"),
    "dead": ("#e9edf3", "#94a3b8", "#475569"),
}


def assign_columns(node_ids, edges, starts):
    """Column of each state: its distance from the initial states (BFS)."""
    adjacency = {}
    for source, target in edges:
        adjacency.setdefault(source, []).append(target)

    column = {}
    queue = deque()
    for node in starts:
        column[node] = 0
        queue.append(node)
    while queue:
        node = queue.popleft()
        for target in adjacency.get(node, ()):
            if target not in column:
                column[target] = column[node] + 1
                queue.append(target)

    # States that cannot be reached from S (only possible in the NFA) go last.
    last = max(column.values(), default=-1) + 1
    for node in node_ids:
        column.setdefault(node, last)
    return column


def order_columns(node_ids, edges, column):
    """Group the states by column and sort each one to reduce edge crossings.

    Barycenter heuristic: a state is moved to the average height of the states
    it is connected to. Sweeping forwards and backwards several times settles
    the columns into an order where most transitions can be drawn straight.
    """
    columns = {}
    for node in node_ids:
        columns.setdefault(column[node], []).append(node)
    ordered = [columns[key] for key in sorted(columns)]

    neighbours = {"back": {}, "forward": {}}
    for source, target in edges:
        if source != target:
            neighbours["back"].setdefault(target, []).append(source)
            neighbours["forward"].setdefault(source, []).append(target)

    def sweep(groups, side):
        position = {node: i for group in ordered for i, node in enumerate(group)}
        for group in groups:
            group.sort(key=lambda node: (
                sum(position.get(other, position[node])
                    for other in neighbours[side].get(node, ()))
                / max(len(neighbours[side].get(node, ())), 1),
                position[node],
            ))

    for _ in range(4):
        sweep(ordered[1:], "back")        # settle each column against the left
        sweep(ordered[-2::-1], "forward")  # and then against the right
    return ordered


def place(ordered):
    """Assign (x, y) to every state and return the size of the drawing."""
    height = max(len(group) for group in ordered)
    positions, rows = {}, {}
    for col, group in enumerate(ordered):
        offset = (height - len(group)) / 2.0
        for row, node in enumerate(group):
            positions[node] = (PAD_X + col * COL_W,
                               PAD_TOP + (offset + row) * ROW_H)
            rows[node] = offset + row
    width = PAD_X * 2 + (len(ordered) - 1) * COL_W
    total = PAD_TOP + PAD_BOTTOM + (height - 1) * ROW_H
    return positions, rows, width, total


def edge_label(x, y, text, bounds):
    """A transition label with a white plate behind it, so it stays readable."""
    width = 7.6 * len(text) + 10
    bounds.append((x - width / 2, y - 10))
    bounds.append((x + width / 2, y + 10))
    return (
        "<rect x='%.1f' y='%.1f' width='%.1f' height='19' rx='6' "
        "fill='#ffffff' stroke='#e2e8f0'/>"
        "<text x='%.1f' y='%.1f' class='elab'>%s</text>"
        % (x - width / 2, y - 9.5, width, x, y + 4.2, html.escape(text))
    )


def self_loop(x, y, text, bounds):
    """A loop drawn above its state, well clear of the other transitions."""
    top = y - RADIUS - 46
    bounds.append((x - 52, top - 6))
    bounds.append((x + 52, y))
    path = ("M %.1f %.1f C %.1f %.1f, %.1f %.1f, %.1f %.1f"
            % (x - 15, y - RADIUS + 5,
               x - 52, top,
               x + 52, top,
               x + 15, y - RADIUS + 5))
    return ("<path d='%s' class='edge'/>%s"
            % (path, edge_label(x, top + 16, text, bounds)))


def bezier_edge(start, end, controls, text, bounds):
    """An arrow from one state to another through the given control points.

    One control point draws a quadratic curve, two draw a cubic one; in both
    cases the ends are trimmed so the arrow touches the border of the circles.
    """
    (x0, y0), (x1, y1) = start, end
    first, last = controls[0], controls[-1]

    dx, dy = first[0] - x0, first[1] - y0
    length = math.hypot(dx, dy) or 1.0
    sx, sy = x0 + dx / length * RADIUS, y0 + dy / length * RADIUS
    dx, dy = x1 - last[0], y1 - last[1]
    length = math.hypot(dx, dy) or 1.0
    ex, ey = x1 - dx / length * (RADIUS + 8), y1 - dy / length * (RADIUS + 8)

    if len(controls) == 1:
        (cx, cy) = controls[0]
        path = "M %.1f %.1f Q %.1f %.1f, %.1f %.1f" % (sx, sy, cx, cy, ex, ey)
        mid = ((x0 + 2 * cx + x1) / 4.0, (y0 + 2 * cy + y1) / 4.0)
    else:
        (cx0, cy0), (cx1, cy1) = controls
        path = ("M %.1f %.1f C %.1f %.1f, %.1f %.1f, %.1f %.1f"
                % (sx, sy, cx0, cy0, cx1, cy1, ex, ey))
        mid = ((x0 + 3 * cx0 + 3 * cx1 + x1) / 8.0,
               (y0 + 3 * cy0 + 3 * cy1 + y1) / 8.0)

    bounds.extend(controls)
    return ("<path d='%s' class='edge'/>%s"
            % (path, edge_label(mid[0], mid[1], text, bounds)))


def bus_edge(start, end, lane_y, text, bounds):
    """An arrow that leaves its state sideways, runs along a free horizontal
    lane above or below every state, and comes back into the target.

    The two vertical parts sit in the gap between columns, so this route never
    touches a state.
    """
    (x0, y0), (x1, y1) = start, end
    step = 1 if x1 > x0 else -1
    turn0 = x0 + step * TURN
    turn1 = x1 - step * TURN
    sx, sy = x0 + step * RADIUS, y0
    ex, ey = x1 - step * (RADIUS + 8), y1

    path = ("M %.1f %.1f C %.1f %.1f, %.1f %.1f, %.1f %.1f "
            "L %.1f %.1f C %.1f %.1f, %.1f %.1f, %.1f %.1f"
            % (sx, sy, turn0, y0, turn0, lane_y, turn0, lane_y,
               turn1, lane_y,
               turn1, lane_y, turn1, y1, ex, ey))
    bounds.append((turn0, lane_y))
    bounds.append((turn1, lane_y))
    return ("<path d='%s' class='edge'/>%s"
            % (path, edge_label((turn0 + turn1) / 2.0, lane_y, text, bounds)))


def free_level(placed, first, last):
    """Lowest lane not used by another arrow covering the same columns.

    Arrows routed over (or under) the states are stacked in lanes so that two
    of them never share the same path.
    """
    used = {lane for (a, b, lane) in placed if not (b < first or a > last)}
    lane = 0
    while lane in used:
        lane += 1
    placed.append((first, last, lane))
    return lane


def quadratic_points(start, control, end):
    """Twenty points along a quadratic curve, enough to test what it touches."""
    points = []
    for step in range(21):
        t = step / 20.0
        u = 1 - t
        points.append((u * u * start[0] + 2 * u * t * control[0] + t * t * end[0],
                       u * u * start[1] + 2 * u * t * control[1] + t * t * end[1]))
    return points


def runs_over_a_state(start, control, end, pos, node_ids):
    """True when the curve would be drawn on top of some other state."""
    for x, y in quadratic_points(start, control, end):
        for node in node_ids:
            nx, ny = pos[node]
            if math.hypot(x - nx, y - ny) < RADIUS + 3                     and math.hypot(start[0] - nx, start[1] - ny) > RADIUS + 3                     and math.hypot(end[0] - nx, end[1] - ny) > RADIUS + 3:
                return True
    return False


def bus_lane(source, target, pos, column, columns, lanes):
    """Height of a free horizontal lane: above the states, or below them when
    the arrow goes backwards."""
    first, last = sorted((column[source], column[target]))
    band = [pos[node][1] for node in columns if first <= column[node] <= last]
    if column[target] < column[source]:
        lane = free_level(lanes["below"], first, last)
        return max(band) + RADIUS + 44 + 30 * lane
    lane = free_level(lanes["above"], first, last)
    return min(band) - RADIUS - 44 - 30 * lane


def crosses(first, second):
    """Number of times two polylines cross each other."""
    def side(p, q, r):
        return (q[1] - p[1]) * (r[0] - q[0]) - (q[0] - p[0]) * (r[1] - q[1])

    total = 0
    for i in range(len(first) - 1):
        a, b = first[i], first[i + 1]
        for j in range(len(second) - 1):
            c, d = second[j], second[j + 1]
            if (side(a, b, c) > 0) != (side(a, b, d) > 0) \
                    and (side(c, d, a) > 0) != (side(c, d, b) > 0):
                total += 1
    return total


def offset_control(start, end, offset):
    """Control point of a curve that bulges `offset` pixels off the straight line."""
    (x0, y0), (x1, y1) = start, end
    mx, my = (x0 + x1) / 2.0, (y0 + y1) / 2.0
    if not offset:
        return (mx, my)
    dx, dy = x1 - x0, y1 - y0
    dist = math.hypot(dx, dy) or 1.0
    return (mx - dy / dist * 2 * offset, my + dx / dist * 2 * offset)


def bus_points(start, end, lane_y):
    """The polyline a lane route follows, used to count crossings."""
    (x0, y0), (x1, y1) = start, end
    step = 1 if x1 > x0 else -1
    return [start, (x0 + step * TURN, y0), (x0 + step * TURN, lane_y),
            (x1 - step * TURN, lane_y), (x1 - step * TURN, y1), end]


def choose_route(source, target, pos, column, edges, node_ids, lanes, drawn):
    """Pick how to draw one arrow.

    A straight arrow is always preferred; if it would run over a state, wider
    and wider curves are tried, and the one crossing the fewest arrows already
    drawn wins. Only when nothing is clean does the arrow take a lane above or
    below every state.
    """
    start, end = pos[source], pos[target]
    opposite = (target, source) in edges
    best = None
    for offset in CANDIDATE_OFFSETS:
        if offset == 0 and opposite:
            continue                     # both directions need their own arc
        control = offset_control(start, end, offset)
        if runs_over_a_state(start, control, end, pos, node_ids):
            continue
        points = quadratic_points(start, control, end)
        score = (sum(crosses(points, other) for other in drawn), abs(offset))
        if best is None or score < best[0]:
            best = (score, ("curve", [control]), points)
        if score[0] == 0 and not offset:
            break                        # a clean straight arrow, nothing better
    if best is not None:
        return best[1], best[2]

    lane_y = bus_lane(source, target, pos, column, node_ids, lanes)
    return ("bus", lane_y), bus_points(start, end, lane_y)


def render_svg(node_ids, labels, kinds, edges, starts):
    """Draw a whole automaton as an SVG element.

    node_ids -- states, in the order they should be considered
    labels   -- text shown inside each state
    kinds    -- "plain", "final" or "dead" per state
    edges    -- {(source, target): [symbols]}
    starts   -- states with an incoming initial arrow
    """
    column = assign_columns(node_ids, edges, starts)
    ordered = order_columns(node_ids, edges, column)
    pos, rows, width, height = place(ordered)

    bounds = [(0, 0), (width, height)]
    body = []
    lanes = {"above": [], "below": [], "side": []}

    # Self-loops are drawn first: every other arrow has to keep away from them.
    loops = {}
    for source, target in edges:
        if source == target:
            x, y = pos[source]
            loops[source] = [(x - 15, y - RADIUS + 5), (x - 40, y - RADIUS - 40),
                             (x + 40, y - RADIUS - 40), (x + 15, y - RADIUS + 5)]

    # Route the arrows shortest first and then refine: on the second pass each
    # arrow is routed again knowing where all the others ended up, which is
    # what removes the crossings the first pass could not foresee.
    plan = [edge for edge in edges if edge[0] != edge[1]]
    plan.sort(key=lambda e: (abs(column[e[1]] - column[e[0]]),
                             column[e[0]], str(e[0]), str(e[1])))
    routes = {}
    for _ in range(2):
        for edge in plan:
            others = list(loops.values())
            others += [points for other, (_, points) in routes.items()
                       if other != edge]
            routes[edge] = choose_route(edge[0], edge[1], pos, column,
                                        edges, node_ids, lanes, others)

    for source in sorted(loops, key=str):
        x, y = pos[source]
        body.append(self_loop(x, y, ",".join(edges[(source, source)]), bounds))
    for edge in plan:
        (kind, shape), _ = routes[edge]
        text = ",".join(edges[edge])
        if kind == "bus":
            body.append(bus_edge(pos[edge[0]], pos[edge[1]], shape, text, bounds))
        else:
            body.append(bezier_edge(pos[edge[0]], pos[edge[1]], shape, text, bounds))

    for node in starts:
        x, y = pos[node]
        bounds.append((x - RADIUS - 44, y))
        body.append("<path d='M %.1f %.1f L %.1f %.1f' class='edge start'/>"
                    % (x - RADIUS - 40, y, x - RADIUS - 7, y))

    for node in node_ids:
        x, y = pos[node]
        fill, stroke, ink = NODE_STYLE[kinds[node]]
        dash = " stroke-dasharray='5 4'" if kinds[node] == "dead" else ""
        body.append("<circle cx='%.1f' cy='%.1f' r='%d' fill='%s' stroke='%s' "
                    "stroke-width='2.5'%s/>" % (x, y, RADIUS, fill, stroke, dash))
        if kinds[node] == "final":
            body.append("<circle cx='%.1f' cy='%.1f' r='%d' fill='none' "
                        "stroke='%s' stroke-width='2'/>" % (x, y, RADIUS - 5, stroke))
        body.append("<text x='%.1f' y='%.1f' class='nlab' fill='%s'>%s</text>"
                    % (x, y + 5, ink, html.escape(labels[node])))

    # The view box follows whatever was drawn, so nothing is ever cut off.
    left = min(p[0] for p in bounds) - 16
    top = min(p[1] for p in bounds) - 16
    box_w = max(p[0] for p in bounds) + 16 - left
    box_h = max(p[1] for p in bounds) + 16 - top

    return (
        "<svg viewBox='%.0f %.0f %.0f %.0f' width='%.0f' height='%.0f' "
        "class='automaton' xmlns='http://www.w3.org/2000/svg'>"
        "<defs><marker id='arrow' viewBox='0 0 10 10' refX='9' refY='5' "
        "markerWidth='7' markerHeight='7' orient='auto-start-reverse'>"
        "<path d='M 0 0 L 10 5 L 0 10 z' fill='#7c8798'/></marker></defs>"
        "%s</svg>" % (left, top, box_w, box_h, box_w, box_h, "".join(body))
    )


def nfa_svg(nfa):
    """Diagram of the input NFA."""
    node_ids = list(range(1, nfa["n"] + 1))
    labels = {q: str(q) for q in node_ids}
    kinds = {q: ("final" if q in nfa["final"] else "plain") for q in node_ids}
    edges = {}
    for (state, symbol), targets in sorted(nfa["delta"].items()):
        for target in sorted(targets):
            edges.setdefault((state, target), []).append(symbol)
    return render_svg(node_ids, labels, kinds, edges, sorted(nfa["initial"]))


def dfa_svg(dfa, names):
    """Diagram of the DFA, with only the reachable states and their new names."""
    node_ids = list(dfa["reachable"])
    labels = {s: names[s] for s in node_ids}
    kinds = {}
    for subset in node_ids:
        if subset in dfa["final"]:
            kinds[subset] = "final"
        elif not subset:
            kinds[subset] = "dead"
        else:
            kinds[subset] = "plain"
    edges = {}
    for subset in node_ids:
        for symbol in dfa["alphabet"]:
            target = dfa["transitions"][(subset, symbol)]
            edges.setdefault((subset, target), []).append(symbol)
    return render_svg(node_ids, labels, kinds, edges, [dfa["initial"]])


def legend_html(dfa, names):
    """Chips mapping every reachable DFA state to the subset it represents."""
    chips = []
    for subset in dfa["reachable"]:
        kind = "chip"
        if subset == dfa["initial"]:
            kind += " chip-initial"
        elif subset in dfa["final"]:
            kind += " chip-final"
        chips.append("<span class='%s'><b>%s</b> = %s</span>"
                     % (kind, names[subset], html.escape(set_to_text(subset))))
    return "<div class='legend'>%s</div>" % "".join(chips)


def marks_html(is_initial, is_final):
    marks = []
    if is_initial:
        marks.append("<span class='m-init' title='initial state'>&rarr;</span>")
    if is_final:
        marks.append("<span class='m-final' title='final state'>&larr;</span>")
    return " ".join(marks)


def nfa_table_html(nfa):
    head = "".join("<th>%s</th>" % html.escape(a) for a in nfa["alphabet"])
    rows = []
    for state in range(1, nfa["n"] + 1):
        cells = "".join(
            "<td>%s</td>" % html.escape(set_to_text(nfa["delta"][(state, a)]))
            for a in nfa["alphabet"]
        )
        classes = []
        if state in nfa["initial"]:
            classes.append("row-initial")
        if state in nfa["final"]:
            classes.append("row-final")
        rows.append("<tr class='%s'><td class='mark'>%s</td><td class='name'>%d</td>%s</tr>"
                    % (" ".join(classes),
                       marks_html(state in nfa["initial"], state in nfa["final"]),
                       state, cells))
    return ("<table><thead><tr><th></th><th>state</th>%s</tr></thead>"
            "<tbody>%s</tbody></table>" % (head, "".join(rows)))


def dfa_table_html(dfa, names, states):
    head = "".join("<th>%s</th>" % html.escape(a) for a in dfa["alphabet"])
    rows = []
    for subset in states:
        is_initial = subset == dfa["initial"]
        is_final = subset in dfa["final"]
        cells = "".join(
            "<td>%s</td>" % names[dfa["transitions"][(subset, a)]]
            for a in dfa["alphabet"]
        )
        classes = []
        if is_initial:
            classes.append("row-initial")
        if is_final:
            classes.append("row-final")
        rows.append("<tr class='%s'><td class='mark'>%s</td><td class='name'>%s</td>"
                    "<td>%s</td>%s</tr>"
                    % (" ".join(classes), marks_html(is_initial, is_final),
                       names[subset], html.escape(set_to_text(subset)), cells))
    return ("<table><thead><tr><th></th><th>M</th><th>subset of Q</th>%s</tr></thead>"
            "<tbody>%s</tbody></table>" % (head, "".join(rows)))


CASE_TEMPLATE = """
<section>
  <header class="case-head">
    <h2>Case %(index)d</h2>
    <div class="stats">
      <span class="stat"><b>%(n)d</b> states of N</span>
      <span class="stat"><b>%(sigma)d</b> symbols</span>
      <span class="stat"><b>%(total)d</b> subsets (2<sup>%(n)d</sup>)</span>
      <span class="stat stat-accent"><b>%(reach)d</b> reachable in M</span>
    </div>
  </header>
  <div class="grid">
    <div class="panel">
      <h3><span class="tag tag-nfa">NFA</span> N &mdash; the input automaton</h3>
      <div class="diagram">%(nfa_diagram)s</div>
      <h4>Transition table of N</h4>
      %(nfa_table)s
    </div>
    <div class="panel">
      <h3><span class="tag tag-dfa">DFA</span> M &mdash; reachable states</h3>
      <div class="diagram">%(dfa_diagram)s</div>
      %(legend)s
      <h4>Reachable states of M <span class="count">%(reach)d</span></h4>
      <p class="hint">These are the states the automaton can actually be in; they are
      the ones drawn in the diagram above.</p>
      <div class="scroll">%(dfa_table_live)s</div>
      %(note)s
      %(dead_block)s
    </div>
  </div>
</section>"""


DEAD_TEMPLATE = """
      <details class="dead">
        <summary>Unreachable states of M <span class="count count-dead">%(count)d</span>
        &mdash; produced by the construction but never entered</summary>
        <p class="hint">The construction builds every subset of Q. These ones cannot be
        reached from the initial state by any string, so they are dead weight: they are
        listed here for completeness and left out of the diagram.</p>
        <div class="scroll">%(table)s</div>
      </details>"""


def render_html(report):
    """Write output.html with one section per case."""
    sections = []
    for i, (nfa, dfa, names, table_states, truncated) in enumerate(report, start=1):
        reachable = set(dfa["reachable"])
        live_states = [s for s in table_states if s in reachable]
        dead_states = [s for s in table_states if s not in reachable]
        dead_block = ""
        if dead_states:
            dead_block = DEAD_TEMPLATE % {
                "count": len(dead_states),
                "table": dfa_table_html(dfa, names, dead_states),
            }
        note = ""
        if truncated:
            note = ("<p class='note'>The power set has 2<sup>%d</sup> states, too many "
                    "to list; only the reachable states are shown.</p>" % nfa["n"])
        sections.append(CASE_TEMPLATE % {
            "index": i,
            "n": nfa["n"],
            "sigma": len(nfa["alphabet"]),
            "total": len(dfa["states"]),
            "reach": len(dfa["reachable"]),
            "nfa_diagram": nfa_svg(nfa),
            "nfa_table": nfa_table_html(nfa),
            "dfa_diagram": dfa_svg(dfa, names),
            "legend": legend_html(dfa, names),
            "note": note,
            "dfa_table_live": dfa_table_html(dfa, names, live_states),
            "dead_block": dead_block,
        })

    page = PAGE_TEMPLATE.replace("<!--SECTIONS-->", "\n".join(sections))
    with open(OUTPUT_HTML, "w", encoding="utf-8") as handle:
        handle.write(page)


PAGE_TEMPLATE = """<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Subset Construction &mdash; NFA to DFA</title>
<style>
  :root {
    --ink: #0f172a;
    --muted: #64748b;
    --line: #e2e8f0;
    --card: #ffffff;
    --indigo: #4f46e5;
    --indigo-soft: #eef2ff;
    --green: #15803d;
    --green-soft: #dcfce7;
  }
  * { box-sizing: border-box; }
  body {
    margin: 0;
    padding: 0 1.25rem 4rem;
    font-family: "Segoe UI", system-ui, -apple-system, sans-serif;
    color: var(--ink);
    background:
      radial-gradient(1200px 520px at 12% -8%, #dbeafe 0%, transparent 60%),
      radial-gradient(1000px 500px at 88% 4%, #ede9fe 0%, transparent 62%),
      radial-gradient(900px 600px at 50% 108%, #ccfbf1 0%, transparent 58%),
      #f7f9ff;
    background-attachment: fixed;
    line-height: 1.55;
  }
  .wrap { max-width: 1280px; margin: 0 auto; }
  header.page {
    background: linear-gradient(120deg, #4338ca 0%, #7c3aed 45%, #0ea5e9 100%);
    color: #fff;
    border-radius: 0 0 22px 22px;
    padding: 2.6rem 2rem 2.2rem;
    margin: 0 -1.25rem 2.2rem;
    text-align: center;
    box-shadow: 0 14px 36px rgba(67, 56, 202, .28);
  }
  header.page .wrap { max-width: 1280px; }
  header.page h1 {
    margin: 0 0 .5rem; font-size: 2.15rem; letter-spacing: -.02em;
    text-shadow: 0 2px 12px rgba(0, 0, 0, .18);
  }
  header.page p {
    margin: .35rem auto 0; max-width: 74ch; color: #e8e6ff; font-size: .96rem;
  }
  header.page code { background: rgba(255,255,255,.18); padding: 0 .3rem; border-radius: 4px; }
  .subtitle {
    font-weight: 600; letter-spacing: .04em; text-transform: uppercase;
    font-size: .82rem !important; color: #c7d2fe !important;
  }

  section {
    position: relative; overflow: hidden;
    background: var(--card);
    border: 1px solid #e6e9f5;
    border-radius: 16px;
    padding: 1.4rem 1.5rem 1.6rem;
    margin-bottom: 1.8rem;
    box-shadow: 0 8px 24px rgba(30, 41, 59, .07);
  }
  section::before {
    content: ""; position: absolute; top: 0; left: 0; right: 0; height: 5px;
    background: linear-gradient(90deg, #4338ca, #7c3aed, #0ea5e9);
  }
  .case-head {
    display: flex; flex-wrap: wrap; align-items: center; gap: .8rem 1.2rem;
    border-bottom: 1px solid var(--line); padding-bottom: .8rem; margin-bottom: 1rem;
  }
  .case-head h2 { margin: 0; font-size: 1.3rem; }
  .stats { display: flex; flex-wrap: wrap; gap: .45rem; margin-left: auto; }
  .stat {
    background: #f1f5f9; color: var(--muted); border-radius: 999px;
    padding: .18rem .7rem; font-size: .82rem;
  }
  .stat b { color: var(--ink); }
  .stat-accent { background: var(--indigo-soft); color: var(--indigo); }
  .stat-accent b { color: var(--indigo); }

  .grid { display: flex; gap: 1.6rem; flex-wrap: wrap; align-items: flex-start; }
  .panel { flex: 1 1 460px; min-width: 340px; }
  .panel h3 { display: flex; align-items: center; gap: .5rem; font-size: 1.02rem; margin: .2rem 0 .7rem; }
  .panel h4 { font-size: .88rem; text-transform: uppercase; letter-spacing: .07em;
              color: var(--muted); margin: 1.1rem 0 .4rem; }
  .tag {
    font-size: .72rem; font-weight: 700; letter-spacing: .06em;
    padding: .15rem .5rem; border-radius: 6px; color: #fff;
  }
  .tag-nfa { background: #0ea5e9; }
  .tag-dfa { background: var(--indigo); }

  .diagram {
    background:
      radial-gradient(circle at 1px 1px, #dbe2f0 1px, transparent 0) 0 0 / 18px 18px,
      #fdfdff;
    border: 1px solid var(--line); border-radius: 12px;
    padding: 1rem; overflow: auto; min-height: 240px;
    display: flex; align-items: center; justify-content: center;
  }
  svg.automaton { max-width: 100%; height: auto; display: block; }
  svg.automaton .edge {
    fill: none; stroke: #7c8798; stroke-width: 1.8;
    marker-end: url(#arrow);
  }
  svg.automaton .nlab {
    font-family: ui-monospace, "Cascadia Mono", Consolas, monospace;
    font-size: 15px; font-weight: 700; text-anchor: middle;
  }
  svg.automaton .elab {
    font-family: ui-monospace, "Cascadia Mono", Consolas, monospace;
    font-size: 12.5px; font-weight: 700; fill: #334155; text-anchor: middle;
  }

  .legend { display: flex; flex-wrap: wrap; gap: .35rem; margin-top: .7rem; }
  .chip {
    font-family: ui-monospace, "Cascadia Mono", monospace; font-size: .78rem;
    background: #f1f5f9; color: #334155; border: 1px solid var(--line);
    border-radius: 6px; padding: .12rem .45rem;
  }
  .chip-initial { background: var(--indigo-soft); border-color: #c7d2fe; color: var(--indigo); }
  .chip-final { background: var(--green-soft); border-color: #bbf7d0; color: var(--green); }

  .count {
    display: inline-block; background: var(--indigo-soft); color: var(--indigo);
    border-radius: 999px; padding: 0 .5rem; font-size: .8rem; margin-left: .25rem;
  }
  .count-dead { background: #f1f5f9; color: var(--muted); }
  .hint { color: var(--muted); font-size: .82rem; margin: .1rem 0 .5rem; }
  details.dead {
    margin-top: 1.1rem; border: 1px dashed #cbd5e1; border-radius: 10px;
    padding: .6rem .8rem; background: #fafbfc;
  }
  details.dead summary {
    cursor: pointer; font-size: .88rem; font-weight: 600; color: var(--muted);
  }
  details.dead[open] summary { margin-bottom: .4rem; }
  .scroll { max-height: 420px; overflow: auto; border-radius: 10px; }
  table {
    border-collapse: separate; border-spacing: 0; width: 100%;
    font-family: ui-monospace, "Cascadia Mono", monospace; font-size: .85rem;
    background: #fff;
  }
  thead th {
    position: sticky; top: 0; z-index: 1;
    background: #f8fafc; color: var(--muted); font-weight: 700;
    border-bottom: 2px solid var(--line); padding: .4rem .7rem; text-align: center;
  }
  tbody td { border-bottom: 1px solid #f1f5f9; padding: .3rem .7rem; text-align: center; }
  tbody tr:hover td { background: #f8faff; }
  td.name { font-weight: 700; }
  td.mark { border: none; background: none; width: 2.6rem; font-size: 1rem; }
  .m-init { color: var(--indigo); font-weight: 700; }
  .m-final { color: var(--green); font-weight: 700; }
  tr.row-initial td.name { color: var(--indigo); }
  tr.row-final td.name { color: var(--green); }

  .note { color: #b45309; background: #fffbeb; border: 1px solid #fde68a;
          border-radius: 8px; padding: .4rem .7rem; font-size: .85rem; }
  footer {
    color: #4c5a70; font-size: .85rem; text-align: center; padding: 1.2rem 0 0;
  }
  footer code { background: #e8ecff; padding: 0 .3rem; border-radius: 4px; }
  @media (max-width: 860px) { .stats { margin-left: 0; } }
</style>
</head>
<body>
<header class="page">
  <div class="wrap">
    <h1>Subset Construction &mdash; NFA &rarr; DFA</h1>
    <p class="subtitle">Kozen 1997, <em>Automata and Computability</em>, Lecture 6</p>
    <p>For each case the input automaton <em>N</em> is shown next to the deterministic
    automaton <em>M</em> built with <code>&delta;(A, a) = &bigcup; &Delta;(q, a)</code>.
    The diagram of <em>M</em> draws only the states reachable from the initial state and
    labels them with their new name; the table lists the states exactly as the
    construction produces them, renamed <code>A0, A1, &hellip;</code>
    &rarr; marks the initial state and &larr; the final states.</p>
  </div>
</header>
<div class="wrap">
<!--SECTIONS-->
<footer>Generated by <code>main.py</code> &mdash; SI2002 Formal Languages, Universidad EAFIT.</footer>
</div>
</body>
</html>
"""


# --------------------------------------------------------------------------

def main():
    if len(sys.argv) > 1:
        with open(sys.argv[1], encoding="utf-8") as handle:
            text = handle.read()
    else:
        text = sys.stdin.read()
    text = text.lstrip("﻿")

    report = []
    for nfa in read_cases(text):
        dfa = subset_construction(nfa)
        truncated = nfa["n"] > FULL_TABLE_LIMIT
        table_states = dfa["reachable"] if truncated else dfa["states"]
        names = name_states(dfa["states"])
        print_dfa(dfa, names, table_states)
        report.append((nfa, dfa, names, table_states, truncated))

    render_html(report)


if __name__ == "__main__":
    main()
