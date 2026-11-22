#!/usr/bin/env python3
"""Writes edge-contracted-icosahedron.svg: the minimizer for 11 points, rotating about its axis.

    python3 Visualization/make_svg.py

The picture is an animated SVG without scripts. It shows the table `X₀` of `Showcase.lean`, which agrees
with the minimizer up to 10^-10. Numerically the configuration is mapped to itself by a rotation of 180
degrees about the axis through one of its points, so the animation only stores a turn of 180 degrees and
repeats it: every point then stands where its partner stood, and the picture is the same. Between the
stored positions the browser interpolates. The program uses the standard library of Python only.
"""
import itertools
import math
import os

# ---- the configuration ----------------------------------------------------------------------------
X0 = [  # the table `X₀` of Showcase.lean
    (0.313620689025589, 0.319317483958265, 0.894247397454238),
    (0.122131934022939, -0.879707882375786, 0.459562653375714),
    (0.836384234608648, 0.540732019932700, 0.089834819071496),
    (-0.829513636587083, -0.542301295299786, -0.133478207330809),
    (-0.566960498580477, 0.239819275605855, -0.788062502659060),
    (0.061432238616290, -0.754530255111397, -0.653383634766071),
    (-0.016529763516812, 0.987228274258469, -0.158452205483935),
    (0.892049358244038, -0.450479658797258, 0.036276982596482),
    (0.482848954144595, 0.189339586942292, -0.854989712393075),
    (-0.513162273240149, -0.211638860342633, 0.831789320751279),
    (-0.786447187737911, 0.558000050679941, 0.264833465295296),
]
ENERGY = "40.596"                        # the minimal energy, rounded
N = len(X0)


def dot(a, b):
    return a[0] * b[0] + a[1] * b[1] + a[2] * b[2]


def sub(a, b):
    return (a[0] - b[0], a[1] - b[1], a[2] - b[2])


def cross(a, b):
    return (a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0])


def unit(a):
    n = math.sqrt(dot(a, a))
    return (a[0] / n, a[1] / n, a[2] / n)


def permutation(images):
    """The permutation of the points that a map of the configuration to itself induces, or None."""
    perm = []
    for q in images:
        j = min(range(N), key=lambda t: math.dist(q, X0[t]))
        if math.dist(q, X0[j]) > 1e-9:
            return None
        perm.append(j)
    return perm if sorted(perm) == list(range(N)) else None


# the axis: the point about which the rotation of 180 degrees maps the configuration to itself
AXES = [i for i in range(N)
        if permutation([sub(tuple(2 * dot(unit(X0[i]), v) * c for c in unit(X0[i])), v) for v in X0])]
assert len(AXES) == 1
POLE = AXES[0]
AXIS = unit(X0[POLE])
HALF_TURN = permutation([sub(tuple(2 * dot(AXIS, v) * c for c in AXIS), v) for v in X0])

# the two mirror planes, which contain the axis
MIRRORS = []
for i, j in itertools.combinations(range(N), 2):
    nrm = unit(sub(X0[i], X0[j]))
    perm = permutation([sub(v, tuple(2 * dot(nrm, v) * c for c in nrm)) for v in X0])
    if perm and all(abs(abs(dot(nrm, m)) - 1) > 1e-6 for m, _ in MIRRORS):
        MIRRORS.append((nrm, perm))
assert len(MIRRORS) == 2 and all(abs(dot(nrm, AXIS)) < 1e-9 for nrm, _ in MIRRORS)

# the orbits of the symmetry group: the point on the axis, three pairs, and four points
ORBIT = list(range(N))
for perm in [HALF_TURN] + [perm for _, perm in MIRRORS]:
    for i in range(N):
        a, b = ORBIT[i], ORBIT[perm[i]]
        ORBIT = [min(a, b) if o in (a, b) else o for o in ORBIT]
SIZE = [ORBIT.count(o) for o in ORBIT]
assert sorted(SIZE) == [1] + [2] * 6 + [4] * 4
QUAD = [i for i in range(N) if SIZE[i] == 4]             # the corners of a rectangle
PAIRS = [i for i in range(N) if SIZE[i] == 2]            # three pairs, each in a mirror plane
assert all(min(abs(dot(nrm, X0[i])) for nrm, _ in MIRRORS) < 1e-9 for i in PAIRS)

# coordinates in which the axis is vertical
E1 = unit(sub(X0[QUAD[0]], tuple(dot(X0[QUAD[0]], AXIS) * c for c in AXIS)))
E2 = cross(AXIS, E1)
BODY = [(dot(p, E1), dot(p, E2), dot(p, AXIS)) for p in X0]


def vertices(theta):
    """The 11 points after a rotation by `theta` about the axis."""
    c, s = math.cos(theta), math.sin(theta)
    return [(c * x - s * y, s * x + c * y, z) for x, y, z in BODY]


FACES = []                               # the 18 triangles of the convex hull, outward orientation
for a, b, c in itertools.combinations(range(N), 3):
    nrm = cross(sub(X0[b], X0[a]), sub(X0[c], X0[a]))
    side = [dot(nrm, sub(X0[q], X0[a])) for q in range(N) if q not in (a, b, c)]
    if all(x < -1e-9 for x in side):
        FACES.append((a, b, c))
    elif all(x > 1e-9 for x in side):
        FACES.append((a, c, b))
assert len(FACES) == 18

EDGES = []                               # (i, j, kind): the 27 edges
for i, j in sorted({tuple(sorted((f[k], f[(k + 1) % 3]))) for f in FACES for k in range(3)}):
    same = ORBIT[i] == ORBIT[j]
    EDGES.append((i, j, "quad" if same and SIZE[i] == 4 else "pair" if same else "side"))
assert len(EDGES) == 27


def is_edge_contracted_icosahedron():
    """The graph of the convex hull is the graph of an icosahedron in which one edge is contracted."""
    ico = {(0, k) for k in range(1, 6)} | {(11, k) for k in range(6, 11)}
    for k in range(5):
        ico |= {(1 + k, 1 + (k + 1) % 5), (6 + k, 6 + (k + 1) % 5), (1 + k, 6 + k), (1 + k, 6 + (k + 1) % 5)}
    merged = {frozenset(0 if v == 1 else v for v in e) for e in ico} - {frozenset((0,))}
    names = sorted({v for e in merged for v in e})
    target = {frozenset(names.index(v) for v in e) for e in merged}
    hull = {frozenset((i, j)) for i, j, _ in EDGES}
    deg_h = [sum(1 for e in hull if v in e) for v in range(N)]
    deg_t = [sum(1 for e in target if v in e) for v in range(N)]

    def extend(image):
        v = len(image)
        if v == N:
            return True
        for w in range(N):
            if w in image or deg_t[w] != deg_h[v]:
                continue
            if all((frozenset((u, v)) in hull) == (frozenset((image[u], w)) in target) for u in range(v)):
                if extend(image + [w]):
                    return True
        return False

    return len(target) == 27 and extend([])


assert is_edge_contracted_icosahedron()

# ---- the picture ----------------------------------------------------------------------------------
W, HEIGHT = 840, 440
CX, CY, RAD = 228, 212, 160              # the centre and the radius of the sphere in the picture
DIST = 6.0                               # the distance of the camera from the centre
ELEV = math.radians(19)                  # its elevation
START = math.radians(14)                 # the rotation of the first picture
BALL = 0.058                             # the radius of a point, in units of the sphere
STEPS = 36                               # stored positions per 180 degrees: every 5 degrees
DUR = "21s"                              # the time of a turn of 180 degrees

PAGE, INK, INK2, MUTED = "#f9f9f7", "#0b0b0b", "#52514e", "#6f6e69"
BLUE, GREEN, NEUTRAL = "#2a78d6", "#149a6b", "#7d7c76"
EDGE, FACE, TINT, RIM = "#6f6e68", "#6a7f9e", "#8794a8", "#5b6b84"
COLOR = {POLE: NEUTRAL, **{i: BLUE for i in QUAD}, **{i: GREEN for i in PAIRS}}
GRAD = {NEUTRAL: "n", BLUE: "b", GREEN: "g"}

FOCAL = RAD * math.sqrt(DIST * DIST - 1)                     # the sphere has the radius RAD
CAM = (math.cos(ELEV), 0.0, math.sin(ELEV))                  # the direction to the camera
RIGHT = (0.0, 1.0, 0.0)
UPV = (-math.sin(ELEV), 0.0, math.cos(ELEV))
LIGHT = (0.45, -0.55, 0.70)                                  # the direction to the light
LIGHT = tuple(c / math.sqrt(sum(x * x for x in LIGHT)) for c in LIGHT)


def smooth(x, lo, hi):
    t = min(1.0, max(0.0, (x - lo) / (hi - lo)))
    return t * t * (3 - 2 * t)


def project(p):
    """The place of a point in the picture, and the scale of lengths at this point."""
    s = FOCAL / (DIST - dot(p, CAM))
    return CX + s * dot(p, RIGHT), CY - s * dot(p, UPV), s


def frame(theta):
    """Everything that the picture shows for one rotation."""
    pts = vertices(theta)
    eye = tuple(DIST * c for c in CAM)
    xy = [project(p) for p in pts]
    # a point is in front if it lies on the side of the sphere that the camera sees
    front = [smooth(dot(p, CAM) - 1 / DIST, -0.035, 0.035) for p in pts]
    facing, shade = [], []
    for a, b, c in FACES:
        n = unit(cross(sub(pts[b], pts[a]), sub(pts[c], pts[a])))
        assert all(dot(n, sub(q, pts[a])) < 1e-9 for q in pts), "the faces are not the convex hull"
        centre = tuple((pts[a][k] + pts[b][k] + pts[c][k]) / 3 for k in range(3))
        facing.append(dot(n, unit(sub(eye, centre))))
        shade.append(max(0.0, dot(n, LIGHT)))
    return pts, xy, front, facing, shade


FRAMES = [frame(START + j * math.pi / STEPS) for j in range(STEPS + 1)]


def num(x, digits=1):
    s = f"{x:.{digits}f}"
    if "." in s:
        s = s.rstrip("0").rstrip(".")
    return "0" if s in ("-0", "") else s


def animate(attr, values):
    """An attribute with its first value, and the animation if the value changes."""
    if all(v == values[0] for v in values):
        return f' {attr}="{values[0]}"', ""
    return (f' {attr}="{values[0]}"',
            f'<animate attributeName="{attr}" dur="{DUR}" repeatCount="indefinite" values="{";".join(values)}"/>')


def element(tag, static, animated):
    attrs, anims = "", ""
    for attr, values in animated:
        a, b = animate(attr, values)
        attrs += a
        anims += b
    return f"<{tag}{static}{attrs}>{anims}</{tag}>" if anims else f"<{tag}{static}{attrs}/>"


def mix(color, other, t):
    a = [int(color[i:i + 2], 16) for i in (1, 3, 5)]
    b = [int(other[i:i + 2], 16) for i in (1, 3, 5)]
    return "#" + "".join(f"{round(x + (y - x) * t):02x}" for x, y in zip(a, b))


def faces():
    out = []
    for f, (a, b, c) in enumerate(FACES):
        pts = [" ".join(f"{num(fr[1][i][0])},{num(fr[1][i][1])}" for i in (a, b, c)) for fr in FRAMES]
        # a face that looks at the camera is shaded by the light, a face on the far side is faint
        op = [num(0.035 + smooth(fr[3][f], -0.04, 0.04) * (0.025 + 0.095 * fr[4][f]), 3) for fr in FRAMES]
        out.append(element("polygon", "", [("points", pts), ("fill-opacity", op)]))
    return out


def edges():
    out = []
    adjacent = {}
    for f, tri in enumerate(FACES):
        for i in range(3):
            adjacent.setdefault(frozenset((tri[i], tri[(i + 1) % 3])), []).append(f)
    for a, b, kind in EDGES:
        fa = adjacent[frozenset((a, b))]
        assert len(fa) == 2
        ds, ops = [], []
        for pts, xy, front, facing, shade in FRAMES:
            (x1, y1, s1), (x2, y2, s2) = xy[a], xy[b]
            # the edge ends at the surfaces of its two points
            length = math.hypot(x2 - x1, y2 - y1)
            ux, uy = (x2 - x1) / length, (y2 - y1) / length
            t1, t2 = BALL * s1 * 0.92, BALL * s2 * 0.92
            ds.append(f"M{num(x1 + ux * t1)} {num(y1 + uy * t1)}L{num(x2 - ux * t2)} {num(y2 - uy * t2)}")
            # an edge is in front if one of its two faces looks at the camera
            vis = smooth(max(facing[fa[0]], facing[fa[1]]), -0.04, 0.04)
            ops.append(num(0.22 + 0.7 * vis, 2))
        cls = {"quad": ' class="u"', "pair": ' class="l"', "side": ""}[kind]
        out.append(element("path", cls, [("d", ds), ("stroke-opacity", ops)]))
    return out


def points(layer):
    """The points of the far side (`layer` 0) or of the near side (`layer` 1).

    A point of the far side is drawn in a paler colour, as if seen through haze, and it is opaque. While
    a point passes the outline of the sphere, its near copy fades in over its far copy."""
    out = []
    for i in range(N):
        near = [fr[2][i] for fr in FRAMES]
        if layer:
            op = [num(v, 2) for v in near]
        else:
            op = ["1" if v < 0.98 else "0" for v in near]
        if all(v == "0" for v in op):
            continue
        cx = [num(fr[1][i][0]) for fr in FRAMES]
        cy = [num(fr[1][i][1]) for fr in FRAMES]
        r = [num(BALL * fr[1][i][2], 2) for fr in FRAMES]
        grad = GRAD[COLOR[i]] + ("" if layer else "f")
        out.append(element("circle", f' fill="url(#{grad})"', [("cx", cx), ("cy", cy), ("r", r), ("opacity", op)]))
    return out


HAZE = "#e7e8ea"                         # the colour towards which the far side fades


def gradient(name, color, haze=0.0):
    stops = [(0, mix(color, "#ffffff", 0.62)), (.45, color), (1, mix(color, "#000000", 0.38))]
    return (f'<radialGradient id="{name}" cx=".34" cy=".3" r=".8">'
            + "".join(f'<stop offset="{num(o, 2)}" stop-color="{mix(c, HAZE, haze)}"/>' for o, c in stops)
            + "</radialGradient>")


TX = 506                                 # the left edge of the text


def legend(y, color, text):
    return (f'<circle cx="{TX + 6}" cy="{y - 5}" r="5.5" fill="url(#{GRAD[color]})"/>'
            f'<text x="{TX + 23}" y="{y}">{text}</text>')


def check_loop():
    """After 180 degrees the picture is the first picture: every point stands where its partner stood."""
    first, last = FRAMES[0], FRAMES[-1]
    tol = 1e-6
    for i in range(N):
        j = HALF_TURN[i]
        assert COLOR[i] == COLOR[j]
        assert all(abs(u - v) < tol for u, v in zip(last[1][i], first[1][j]))
        assert abs(last[2][i] - first[2][j]) < tol
    index = {frozenset(f): k for k, f in enumerate(FACES)}
    for f, tri in enumerate(FACES):
        g = index[frozenset(HALF_TURN[i] for i in tri)]
        assert abs(last[3][f] - first[3][g]) < tol and abs(last[4][f] - first[4][g]) < tol
    kinds = {frozenset((i, j)): kind for i, j, kind in EDGES}
    for (i, j), kind in list(kinds.items()):
        assert kinds[frozenset((HALF_TURN[i], HALF_TURN[j]))] == kind


def svg():
    font = "Inter,system-ui,-apple-system,'Segoe UI',Helvetica,Arial,sans-serif"
    parts = [
        f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {W} {HEIGHT}" width="{W}" height="{HEIGHT}" '
        f'font-family="{font}" role="img" aria-labelledby="t d">',
        '<title id="t">The minimizer for 11 points: an edge-contracted icosahedron</title>',
        '<desc id="d">Eleven points on the unit sphere, rotating about their axis of symmetry: one point on '
        'the axis, three pairs of points in the two mirror planes, and four points that are the corners of a '
        f'rectangle. Its Coulomb energy {ENERGY} is the minimum for 11 points.</desc>',
        "<defs>",
        gradient("b", BLUE), gradient("g", GREEN), gradient("n", NEUTRAL),
        gradient("bf", BLUE, 0.52), gradient("gf", GREEN, 0.52), gradient("nf", NEUTRAL, 0.52),
        f'<radialGradient id="glass"><stop offset="0" stop-color="{TINT}" stop-opacity=".02"/>'
        f'<stop offset=".7" stop-color="{TINT}" stop-opacity=".05"/>'
        f'<stop offset=".92" stop-color="{RIM}" stop-opacity=".13"/>'
        f'<stop offset="1" stop-color="{RIM}" stop-opacity=".34"/></radialGradient>',
        '<radialGradient id="shine"><stop offset="0" stop-color="#fff" stop-opacity=".75"/>'
        '<stop offset=".5" stop-color="#fff" stop-opacity=".22"/>'
        '<stop offset="1" stop-color="#fff" stop-opacity="0"/></radialGradient>',
        '<radialGradient id="shadow"><stop offset="0" stop-color="#141a2a" stop-opacity=".19"/>'
        '<stop offset=".6" stop-color="#141a2a" stop-opacity=".06"/>'
        '<stop offset="1" stop-color="#141a2a" stop-opacity="0"/></radialGradient>',
        "</defs>",
        f'<rect x=".5" y=".5" width="{W - 1}" height="{HEIGHT - 1}" rx="14" fill="{PAGE}" stroke="{INK}" '
        'stroke-opacity=".1"/>',
        f'<ellipse cx="{CX}" cy="{CY + RAD + 25}" rx="{round(RAD * 0.8)}" ry="14" fill="url(#shadow)"/>',
        f'<circle cx="{CX}" cy="{CY}" r="{RAD}" fill="url(#glass)" stroke="{RIM}" stroke-opacity=".28"/>',
        "<g>", *points(0), "</g>",
        f'<g fill="{FACE}">', *faces(), "</g>",
        f'<g fill="none" stroke="{EDGE}" stroke-width="1.4" stroke-linecap="round">',
        f"<style>.u{{stroke:{BLUE};stroke-width:2.1}}.l{{stroke:{GREEN};stroke-width:2.1}}</style>",
        *edges(), "</g>",
        "<g>", *points(1), "</g>",
        f'<ellipse cx="{CX - 64}" cy="{CY - 86}" rx="54" ry="29" transform="rotate(-38 {CX - 64} {CY - 86})" '
        'fill="url(#shine)"/>',
        # the text, in the manner of the page lukasliehr.github.io/energy-minimization
        f'<text x="{TX}" y="92" font-size="13" fill="{MUTED}">Thomson problem for 11 points</text>',
        f'<text font-size="23" font-weight="600" fill="{INK}" letter-spacing="-.35">'
        f'<tspan x="{TX}" y="124">Edge-contracted</tspan><tspan x="{TX}" y="152">icosahedron</tspan></text>',
        f'<g font-size="14" fill="{INK2}">',
        legend(196, NEUTRAL, "One point on the axis"),
        legend(224, GREEN, "Three pairs in the two mirror planes"),
        legend(252, BLUE, "Four corners of a rectangle"),
        "</g>",
        f'<line x1="{TX}" y1="280" x2="{W - 44}" y2="280" stroke="{INK}" stroke-opacity=".1"/>',
        f'<text x="{TX}" y="310" font-size="12" fill="{MUTED}">Minimal Coulomb energy</text>',
        f'<text x="{TX}" y="344" font-size="27" font-weight="600" fill="{INK}" letter-spacing="-.5">{ENERGY}</text>',
        "</svg>",
    ]
    return "\n".join(parts) + "\n"


if __name__ == "__main__":
    path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "edge-contracted-icosahedron.svg")
    check_loop()
    text = svg()
    with open(path, "w", encoding="utf-8") as f:
        f.write(text)
    print(path, len(text.encode()), "bytes")
