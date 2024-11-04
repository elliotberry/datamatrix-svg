/**
	https://github.com/datalog/datamatrix-svg
	under MIT license
	# datamatrix.js has no dependencies
	Copyright (c) 2020 Constantine
*/

function DATAMatrix(Q) {
  var M = [],
    xx = 0,
    yy = 0,
    bit = function (x, y) {
      (M[y] = M[y] || []), (M[y][x] = 1);
    },
    toAscii = function (t) {
      var r = [],
        l = t.length;

      for (var index = 0; index < l; index++) {
        var c = t.charCodeAt(index),
          c1 = index + 1 < l ? t.charCodeAt(index + 1) : 0;

        if (c > 47 && c < 58 && c1 > 47 && c1 < 58) {
          /* 2 digits */

          r.push((c - 48) * 10 + c1 + 82) /* - 48 + 130 = 82 */, index++;
        } else if (c > 127) {
          /* extended char */

          r.push(235), r.push((c - 127) & 255);
        } else r.push(c + 1); /* char */
      }

      return r;
    },
    toBase = function (t) {
      var r = [231] /* switch to Base 256 */,
        l = t.length;

      if (250 < l) {
        r.push((37 + ((l / 250) | 0)) & 255); /* length high byte (in 255 state algo) */
      }

      r.push(((l % 250) + ((149 * (r.length + 1)) % 255) + 1) & 255); /* length low byte (in 255 state algo) */

      for (var index = 0; index < l; index++) {
        r.push((t.charCodeAt(index) + ((149 * (r.length + 1)) % 255) + 1) & 255); /* data in 255 state algo */
      }

      return r;
    },
    toEdifact = function (t) {
      var n = t.length,
        l = (n + 1) & -4,
        cw = 0,
        ch,
        r = l > 0 ? [240] : []; /* switch to Edifact */

      for (var index = 0; index < l; index++) {
        if (index < l - 1) {
          /* encode char */
          ch = t.charCodeAt(index);
          if (ch < 32 || ch > 94) return []; /* not in set */
        } else ch = 31; /* return to ASCII */

        cw = cw * 64 + (ch & 63);

        if ((index & 3) == 3) {
          /* 4 data in 3 words */
          r.push(cw >> 16), r.push((cw >> 8) & 255), r.push(cw & 255), (cw = 0);
        }
      }

      return l > n ? r : r.concat(toAscii(t.slice(l == 0 ? 0 : l - 1))); /* last chars*/
    },
    toText = function (t, s) {
      var index,
        index_,
        cc = 0,
        cw = 0,
        l = t.length,
        r = [s[0]] /* start switch */,
        push = function (v) {
          /* pack 3 chars in 2 codes */
          cw = 40 * cw + v;

          /* add code */
          if (cc++ == 2) {
            r.push(++cw >> 8), r.push(cw & 255), (cc = cw = 0);
          }
        };

      for (index = 0; index < l; index++) {
        /* last char in ASCII is shorter */
        if (0 == cc && index == l - 1) break;

        var ch = t.charCodeAt(index);

        if (ch > 127 && 238 != r[0]) {
          /* extended char */

          push(1), push(30), (ch -= 128); /* hi bit in C40 & TEXT */
        }

        for (index_ = 1; ch > s[index_]; index_ += 3); /* select char set */

        var x = s[index_ + 1]; /* shift */

        if (8 == x || (9 == x && 0 == cc && index == l - 1)) return []; /* char not in set or padding fails */

        if (x < 5 && cc == 2 && index == l - 1) break; /* last char in ASCII */
        if (x < 5) push(x); /* shift */

        push(ch - s[index_ + 2]); /* char offset */
      }

      if (2 == cc && 238 !== r[0]) {
        /* add pad */

        push(0);
      }

      r.push(254); /* return to ASCII */

      if (cc > 0 || index < l) r = r.concat(toAscii(t.slice(index - cc))); /* last chars */

      return r;
    },
    encodeMessage = function (text, rct) {
      text = unescape(encodeURI(text));

      var M = [];

      var enc = toAscii(text),
        element = enc.length,
        k = toText(text, [/* C40 */ 230, 31, 0, 0, 32, 9, 29, 47, 1, 33, 57, 9, 44, 64, 1, 43, 90, 9, 51, 95, 1, 69, 127, 2, 96, 255, 1, 0]),
        l = k.length;
      if (l > 0 && l < element) (enc = k), (element = l);

      k = toText(text, [/* TEXT */ 239, 31, 0, 0, 32, 9, 29, 47, 1, 33, 57, 9, 44, 64, 1, 43, 90, 2, 64, 95, 1, 69, 122, 9, 83, 127, 2, 96, 255, 1, 0]);
      l = k.length;
      if (l > 0 && l < element) (enc = k), (element = l);

      k = toText(text, [/* X12*/ 238, 12, 8, 0, 13, 9, 13, 31, 8, 0, 32, 9, 29, 41, 8, 0, 42, 9, 41, 47, 8, 0, 57, 9, 44, 64, 8, 0, 90, 9, 51, 255, 8, 0]);
      l = k.length;
      if (l > 0 && l < element) (enc = k), (element = l);

      k = toEdifact(text);
      l = k.length;
      if (l > 0 && l < element) (enc = k), (element = l);

      k = toBase(text);
      l = k.length;
      if (l > 0 && l < element) (enc = k), (element = l);

      var h,
        w,
        nc = 1,
        nr = 1,
        fw,
        fh /* symbol size, regions, region size */,
        index,
        index_ = -1,
        c,
        r,
        s,
        b = 1 /* compute symbol size */,
        rs = Array.from({length: 70}) /* reed / solomon code */,
        rc = Array.from({length: 70}),
        lg = Array.from({length: 256}) /* log / exp table for multiplication */,
        ex = Array.from({length: 255});

      if (rct && element < 50) {
        /* rect */

        k = [/* symbol width, checkwords */ 16, 7, 28, 11, 24, 14, 32, 18, 32, 24, 44, 28];

        do {
          w = k[++index_]; /* width */
          h = 6 + (index_ & 12); /* height */
          l = (w * h) / 8; /* bytes count in symbol */
        } while (l - k[++index_] < element); /* could we fill the rect? */

        /* column regions */
        if (w > 25) nc = 2;
      } else {
        /* square */

        w = h = 6;
        index = 2; /* size increment */
        k = [5, 7, 10, 12, 14, 18, 20, 24, 28, 36, 42, 48, 56, 68, 84, 112, 144, 192, 224, 272, 336, 408, 496, 620]; /* rs checkwords */

        do {
          if (++index_ == k.length) return [0, 0]; /* msg is too long */

          if (w > 11 * index) index = (4 + index) & 12; /* advance increment */

          w = h += index;
          l = (w * h) >> 3;
        } while (l - k[index_] < element);

        if (w > 27) nr = nc = 2 * ((w / 54) | 0) + 2; /* regions */
        if (l > 255) b = 2 * (l >> 9) + 2; /* blocks */
      }

      (s = k[index_]) /* rs checkwords */, (fw = w / nc) /* region size */, (fh = h / nr);

      /* first padding */
      if (element < l - s) enc[element++] = 129;

      /* more padding */
      while (element < l - s) {
        enc[element++] = (((149 * element) % 253) + 130) % 254;
      }

      /* Reed Solomon error detection and correction */
      s /= b;

      /* log / exp table of Galois field */
      for (index_ = 1, index = 0; index < 255; index++) {
        (ex[index] = index_), (lg[index_] = index), (index_ += index_);

        if (index_ > 255) index_ ^= 301; /* 301 == a^8 + a^5 + a^3 + a^2 + 1 */
      }

      /* RS generator polynomial */
      for (rs[s] = 0, index = 1; index <= s; index++) for (index_ = s - index, rs[index_] = 1; index_ < s; index_++) rs[index_] = rs[index_ + 1] ^ ex[(lg[rs[index_]] + index) % 255];

      /* RS correction data for each block */
      for (c = 0; c < b; c++) {
        for (index = 0; index <= s; index++) rc[index] = 0;
        for (index = c; index < element; index += b) for (index_ = 0, x = rc[0] ^ enc[index]; index_ < s; index_++) rc[index_] = rc[index_ + 1] ^ (x ? ex[(lg[rs[index_]] + lg[x]) % 255] : 0);

        /* interleaved correction data */
        for (index = 0; index < s; index++) enc[element + c + index * b] = rc[index];
      }

      /* layout perimeter finder pattern */
      /* horizontal */
      for (index = 0; index < h + 2 * nr; index += fh + 2)
        for (index_ = 0; index_ < w + 2 * nc; index_++) {
          bit(index_, index + fh + 1);
          if ((index_ & 1) == 0) bit(index_, index);
        }

      /* vertical */
      for (index = 0; index < w + 2 * nc; index += fw + 2)
        for (index_ = 0; index_ < h; index_++) {
          bit(index, index_ + ((index_ / fh) | 0) * 2 + 1);
          if ((index_ & 1) == 1) bit(index + fw + 1, index_ + ((index_ / fh) | 0) * 2);
        }

      (s = 2) /* step */, (c = 0) /* column */, (r = 4) /* row */, (b = [/* nominal byte layout */ 0, 0, -1, 0, -2, 0, 0, -1, -1, -1, -2, -1, -1, -2, -2, -2]);

      /* diagonal steps */
      for (index = 0; index < l; r -= s, c += s) {
        if (r == h - 3 && c == -1) k = [/* corner A layout */ w, 6 - h, w, 5 - h, w, 4 - h, w, 3 - h, w - 1, 3 - h, 3, 2, 2, 2, 1, 2];
        else if (r == h + 1 && c == 1 && (w & 7) == 0 && (h & 7) == 6) k = [/* corner D layout */ w - 2, -h, w - 3, -h, w - 4, -h, w - 2, -1 - h, w - 3, -1 - h, w - 4, -1 - h, w - 2, -2, -1, -2];
        else {
          if (r == 0 && c == w - 2 && w & 3) continue; /* corner B: omit upper left */
          if (r < 0 || c >= w || r >= h || c < 0) {
            /* outside */

            (s = -s) /* turn around */, (r += 2 + s / 2), (c += 2 - s / 2);

            while (r < 0 || c >= w || r >= h || c < 0) {
              (r -= s), (c += s);
            }
          }
          if (r == h - 2 && c == 0 && w & 3) k = [/* corner B layout */ w - 1, 3 - h, w - 1, 2 - h, w - 2, 2 - h, w - 3, 2 - h, w - 4, 2 - h, 0, 1, 0, 0, 0, -1];
          else if (r == h - 2 && c == 0 && (w & 7) == 4) k = [/* corner C layout */ w - 1, 5 - h, w - 1, 4 - h, w - 1, 3 - h, w - 1, 2 - h, w - 2, 2 - h, 0, 1, 0, 0, 0, -1];
          else if (r == 1 && c == w - 1 && (w & 7) == 0 && (h & 7) == 6) continue; /* omit corner D */
          else k = b; /* nominal L - shape layout */
        }

        /* layout each bit */
        for (element = enc[index++], index_ = 0; element > 0; index_ += 2, element >>= 1) {
          if (element & 1) {
            var x = c + k[index_],
              y = r + k[index_ + 1];

            /* wrap around */
            if (x < 0) (x += w), (y += 4 - ((w + 4) & 7));
            if (y < 0) (y += h), (x += 4 - ((h + 4) & 7));

            /* region gap */
            bit(x + 2 * ((x / fw) | 0) + 1, y + 2 * ((y / fh) | 0) + 1);
          }
        }
      }

      /* unfilled corner */
      for (index = w; index & 3; index--) {
        bit(index, index);
      }

      (xx = w + 2 * nc), (yy = h + 2 * nr);
    };

  return (function () {
    function ishex(c) {
      return /^#[0-9a-f]{3}(?:[0-9a-f]{3})?$/i.test(c);
    }

    function svg(n, a) {
      n = document.createElementNS(ns, n);

      for (var o in a || {}) {
        n.setAttribute(o, a[o]);
      }

      return n;
    }

    var abs = Math.abs,
      r,
      x,
      y,
      d,
      sx,
      sy,
      ns = 'http://www.w3.org/2000/svg',
      path = '',
      q = 'string' == typeof Q ? {msg: Q} : Q || {},
      p = q.pal || ['#000'],
      dm = abs(q.dim) || 256,
      pd = abs(q.pad),
      pd = pd > -1 ? pd : 2,
      mx = [1, 0, 0, 1, pd, pd],
      fg = p[0],
      fg = ishex(fg) ? fg : '#000',
      bg = p[1],
      bg = ishex(bg) ? bg : 0,
      /* render optimized or verbose svg */
      optimized = q.vrb ? 0 : 1;

    encodeMessage(q.msg || '', q.rct);

    (sx = xx + pd * 2), (sy = yy + pd * 2);

    y = yy;

    while (y--) {
      (d = 0), (x = xx);

      while (x--) {
        if (M[y][x]) {
          if (optimized) {
            d++;

            if (!M[y][x - 1]) (path += 'M' + x + ',' + y + 'h' + d + 'v1h-' + d + 'v-1z'), (d = 0);
          } else path += 'M' + x + ',' + y + 'h1v1h-1v-1z';
        }
      }
    }

    r = svg('svg', {
      fill: fg,
      height: dm,
      'shape-rendering': 'crispEdges',
      version: '1.1',
      viewBox: [0, 0, sx, sy].join(' '),
      width: ((dm / sy) * sx) | 0,
      xmlns: ns,
    });

    if (bg)
      r.append(
        svg('path', {
          d: 'M0,0v' + sy + 'h' + sx + 'V0H0Z',
          fill: bg,
        }),
      );

    r.append(
      svg('path', {
        d: path,
        transform: 'matrix(' + mx + ')',
      }),
    );

    return r;
  })();
}
var svgNode = DATAMatrix('Hello World!');
console.log(svgNode.outerHTML);