// CodeMirror, copyright (c) by Marijn Haverbeke and others
// Distributed under an MIT license: http://codemirror.net/LICENSE

// This is CodeMirror (http://codemirror.net), a code editor
// implemented in JavaScript on top of the browser's DOM.
//
// You can find some technical background for some of the code below
// at http://marijnhaverbeke.nl/blog/#cm-internals .

(function(mod) {
  if (typeof exports == "object" && typeof module == "object") // CommonJS
    module.exports = mod();
  else if (typeof define == "function" && define.amd) // AMD
    return define([], mod);
  else // Plain browser env
    (this || window).CodeMirror = mod();
})(function() {
  "use strict";

  // BROWSER SNIFFING

  // Kludges for bugs and behavior differences that can't be feature
  // detected are enabled based on userAgent etc sniffing.
  var userAgent = navigator.userAgent;
  var platform = navigator.platform;

  var gecko = /gecko\/\d/i.test(userAgent);
  var ie_upto10 = /MSIE \d/.test(userAgent);
  var ie_11up = /Trident\/(?:[7-9]|\d{2,})\..*rv:(\d+)/.exec(userAgent);
  var ie = ie_upto10 || ie_11up;
  var ie_version = ie && (ie_upto10 ? document.documentMode || 6 : ie_11up[1]);
  var webkit = /WebKit\//.test(userAgent);
  var qtwebkit = webkit && /Qt\/\d+\.\d+/.test(userAgent);
  var chrome = /Chrome\//.test(userAgent);
  var presto = /Opera\//.test(userAgent);
  var safari = /Apple Computer/.test(navigator.vendor);
  var mac_geMountainLion = /Mac OS X 1\d\D([8-9]|\d\d)\D/.test(userAgent);
  var phantom = /PhantomJS/.test(userAgent);

  var ios = /AppleWebKit/.test(userAgent) && /Mobile\/\w+/.test(userAgent);
  // This is woefully incomplete. Suggestions for alternative methods welcome.
  var mobile = ios || /Android|webOS|BlackBerry|Opera Mini|Opera Mobi|IEMobile/i.test(userAgent);
  var mac = ios || /Mac/.test(platform);
  var chromeOS = /\bCrOS\b/.test(userAgent);
  var windows = /win/i.test(platform);

  var presto_version = presto && userAgent.match(/Version\/(\d*\.\d*)/);
  if (presto_version) presto_version = Number(presto_version[1]);
  if (presto_version && presto_version >= 15) { presto = false; webkit = true; }
  // Some browsers use the wrong event properties to signal cmd/ctrl on OS X
  var flipCtrlCmd = mac && (qtwebkit || presto && (presto_version == null || presto_version < 12.11));
  var captureRightClick = gecko || (ie && ie_version >= 9);

  // Optimize some code when these features are not used.
  var sawReadOnlySpans = false, sawCollapsedSpans = false;

  // EDITOR CONSTRUCTOR

  // A CodeMirror instance represents an editor. This is the object
  // that user code is usually dealing with.

  function CodeMirror(place, options) {
    if (!(this instanceof CodeMirror)) return new CodeMirror(place, options);

    this.options = options = options ? copyObj(options) : {};
    // Determine effective options based on given values and defaults.
    copyObj(defaults, options, false);
    setGuttersForLineNumbers(options);

    var doc = options.value;
    if (typeof doc == "string") doc = new Doc(doc, options.mode, null, options.lineSeparator);
    this.doc = doc;

    var input = new CodeMirror.inputStyles[options.inputStyle](this);
    var display = this.display = new Display(place, doc, input);
    display.wrapper.CodeMirror = this;
    updateGutters(this);
    themeChanged(this);
    if (options.lineWrapping)
      this.display.wrapper.className += " CodeMirror-wrap";
    if (options.autofocus && !mobile) display.input.focus();
    initScrollbars(this);

    this.state = {
      keyMaps: [],  // stores maps added by addKeyMap
      overlays: [], // highlighting overlays, as added by addOverlay
      modeGen: 0,   // bumped when mode/overlay changes, used to invalidate highlighting info
      overwrite: false,
      delayingBlurEvent: false,
      focused: false,
      suppressEdits: false, // used to disable editing during key handlers when in readOnly mode
      pasteIncoming: false, cutIncoming: false, // help recognize paste/cut edits in input.poll
      selectingText: false,
      draggingText: false,
      highlight: new Delayed(), // stores highlight worker timeout
      keySeq: null,  // Unfinished key sequence
      specialChars: null
    };

    var cm = this;

    // Override magic textarea content restore that IE sometimes does
    // on our hidden textarea on reload
    if (ie && ie_version < 11) setTimeout(function() { cm.display.input.reset(true); }, 20);

    registerEventHandlers(this);
    ensureGlobalHandlers();

    startOperation(this);
    this.curOp.forceUpdate = true;
    attachDoc(this, doc);

    if ((options.autofocus && !mobile) || cm.hasFocus())
      setTimeout(bind(onFocus, this), 20);
    else
      onBlur(this);

    for (var opt in optionHandlers) if (optionHandlers.hasOwnProperty(opt))
      optionHandlers[opt](this, options[opt], Init);
    maybeUpdateLineNumberWidth(this);
    if (options.finishInit) options.finishInit(this);
    for (var i = 0; i < initHooks.length; ++i) initHooks[i](this);
    endOperation(this);
    // Suppress optimizelegibility in Webkit, since it breaks text
    // measuring on line wrapping boundaries.
    if (webkit && options.lineWrapping &&
        getComputedStyle(display.lineDiv).textRendering == "optimizelegibility")
      display.lineDiv.style.textRendering = "auto";
  }

  // DISPLAY CONSTRUCTOR

  // The display handles the DOM integration, both for input reading
  // and content drawing. It holds references to DOM nodes and
  // display-related state.

  function Display(place, doc, input) {
    var d = this;
    this.input = input;

    // Covers bottom-right square when both scrollbars are present.
    d.scrollbarFiller = elt("div", null, "CodeMirror-scrollbar-filler");
    d.scrollbarFiller.setAttribute("cm-not-content", "true");
    // Covers bottom of gutter when coverGutterNextToScrollbar is on
    // and h scrollbar is present.
    d.gutterFiller = elt("div", null, "CodeMirror-gutter-filler");
    d.gutterFiller.setAttribute("cm-not-content", "true");
    // Will contain the actual code, positioned to cover the viewport.
    d.lineDiv = elt("div", null, "CodeMirror-code");
    // Elements are added to these to represent selection and cursors.
    d.selectionDiv = elt("div", null, null, "position: relative; z-index: 1");
    d.cursorDiv = elt("div", null, "CodeMirror-cursors");
    // A visibility: hidden element used to find the size of things.
    d.measure = elt("div", null, "CodeMirror-measure");
    // When lines outside of the viewport are measured, they are drawn in this.
    d.lineMeasure = elt("div", null, "CodeMirror-measure");
    // Wraps everything that needs to exist inside the vertically-padded coordinate system
    d.lineSpace = elt("div", [d.measure, d.lineMeasure, d.selectionDiv, d.cursorDiv, d.lineDiv],
                      null, "position: relative; outline: none");
    // Moved around its parent to cover visible view.
    d.mover = elt("div", [elt("div", [d.lineSpace], "CodeMirror-lines")], null, "position: relative");
    // Set to the height of the document, allowing scrolling.
    d.sizer = elt("div", [d.mover], "CodeMirror-sizer");
    d.sizerWidth = null;
    // Behavior of elts with overflow: auto and padding is
    // inconsistent across browsers. This is used to ensure the
    // scrollable area is big enough.
    d.heightForcer = elt("div", null, null, "position: absolute; height: " + scrollerGap + "px; width: 1px;");
    // Will contain the gutters, if any.
    d.gutters = elt("div", null, "CodeMirror-gutters");
    d.lineGutter = null;
    // Actual scrollable element.
    d.scroller = elt("div", [d.sizer, d.heightForcer, d.gutters], "CodeMirror-scroll");
    d.scroller.setAttribute("tabIndex", "-1");
    // The element in which the editor lives.
    d.wrapper = elt("div", [d.scrollbarFiller, d.gutterFiller, d.scroller], "CodeMirror");

    // Work around IE7 z-index bug (not perfect, hence IE7 not really being supported)
    if (ie && ie_version < 8) { d.gutters.style.zIndex = -1; d.scroller.style.paddingRight = 0; }
    if (!webkit && !(gecko && mobile)) d.scroller.draggable = true;

    if (place) {
      if (place.appendChild) place.appendChild(d.wrapper);
      else place(d.wrapper);
    }

    // Current rendered range (may be bigger than the view window).
    d.viewFrom = d.viewTo = doc.first;
    d.reportedViewFrom = d.reportedViewTo = doc.first;
    // Information about the rendered lines.
    d.view = [];
    d.renderedView = null;
    // Holds info about a single rendered line when it was rendered
    // for measurement, while not in view.
    d.externalMeasured = null;
    // Empty space (in pixels) above the view
    d.viewOffset = 0;
    d.lastWrapHeight = d.lastWrapWidth = 0;
    d.updateLineNumbers = null;

    d.nativeBarWidth = d.barHeight = d.barWidth = 0;
    d.scrollbarsClipped = false;

    // Used to only resize the line number gutter when necessary (when
    // the amount of lines crosses a boundary that makes its width change)
    d.lineNumWidth = d.lineNumInnerWidth = d.lineNumChars = null;
    // Set to true when a non-horizontal-scrolling line widget is
    // added. As an optimization, line widget aligning is skipped when
    // this is false.
    d.alignWidgets = false;

    d.cachedCharWidth = d.cachedTextHeight = d.cachedPaddingH = null;

    // Tracks the maximum line length so that the horizontal scrollbar
    // can be kept static when scrolling.
    d.maxLine = null;
    d.maxLineLength = 0;
    d.maxLineChanged = false;

    // Used for measuring wheel scrolling granularity
    d.wheelDX = d.wheelDY = d.wheelStartX = d.wheelStartY = null;

    // True when shift is held down.
    d.shift = false;

    // Used to track whether anything happened since the context menu
    // was opened.
    d.selForContextMenu = null;

    d.activeTouch = null;

    input.init(d);
  }

  // STATE UPDATES

  // Used to get the editor into a consistent state again when options change.

  function loadMode(cm) {
    cm.doc.mode = CodeMirror.getMode(cm.options, cm.doc.modeOption);
    resetModeState(cm);
  }

  function resetModeState(cm) {
    cm.doc.iter(function(line) {
      if (line.stateAfter) line.stateAfter = null;
      if (line.styles) line.styles = null;
    });
    cm.doc.frontier = cm.doc.first;
    startWorker(cm, 100);
    cm.state.modeGen++;
    if (cm.curOp) regChange(cm);
  }

  function wrappingChanged(cm) {
    if (cm.options.lineWrapping) {
      addClass(cm.display.wrapper, "CodeMirror-wrap");
      cm.display.sizer.style.minWidth = "";
      cm.display.sizerWidth = null;
    } else {
      rmClass(cm.display.wrapper, "CodeMirror-wrap");
      findMaxLine(cm);
    }
    estimateLineHeights(cm);
    regChange(cm);
    clearCaches(cm);
    setTimeout(function(){updateScrollbars(cm);}, 100);
  }

  // Returns a function that estimates the height of a line, to use as
  // first approximation until the line becomes visible (and is thus
  // properly measurable).
  function estimateHeight(cm) {
    var th = textHeight(cm.display), wrapping = cm.options.lineWrapping;
    var perLine = wrapping && Math.max(5, cm.display.scroller.clientWidth / charWidth(cm.display) - 3);
    return function(line) {
      if (lineIsHidden(cm.doc, line)) return 0;

      var widgetsHeight = 0;
      if (line.widgets) for (var i = 0; i < line.widgets.length; i++) {
        if (line.widgets[i].height) widgetsHeight += line.widgets[i].height;
      }

      if (wrapping)
        return widgetsHeight + (Math.ceil(line.text.length / perLine) || 1) * th;
      else
        return widgetsHeight + th;
    };
  }

  function estimateLineHeights(cm) {
    var doc = cm.doc, est = estimateHeight(cm);
    doc.iter(function(line) {
      var estHeight = est(line);
      if (estHeight != line.height) updateLineHeight(line, estHeight);
    });
  }

  function themeChanged(cm) {
    cm.display.wrapper.className = cm.display.wrapper.className.replace(/\s*cm-s-\S+/g, "") +
      cm.options.theme.replace(/(^|\s)\s*/g, " cm-s-");
    clearCaches(cm);
  }

  function guttersChanged(cm) {
    updateGutters(cm);
    regChange(cm);
    setTimeout(function(){alignHorizontally(cm);}, 20);
  }

  // Rebuild the gutter elements, ensure the margin to the left of the
  // code matches their width.
  function updateGutters(cm) {
    var gutters = cm.display.gutters, specs = cm.options.gutters;
    removeChildren(gutters);
    for (var i = 0; i < specs.length; ++i) {
      var gutterClass = specs[i];
      var gElt = gutters.appendChild(elt("div", null, "CodeMirror-gutter " + gutterClass));
      if (gutterClass == "CodeMirror-linenumbers") {
        cm.display.lineGutter = gElt;
        gElt.style.width = (cm.display.lineNumWidth || 1) + "px";
      }
    }
    gutters.style.display = i ? "" : "none";
    updateGutterSpace(cm);
  }

  function updateGutterSpace(cm) {
    var width = cm.display.gutters.offsetWidth;
    cm.display.sizer.style.marginLeft = width + "px";
  }

  // Compute the character length of a line, taking into account
  // collapsed ranges (see markText) that might hide parts, and join
  // other lines onto it.
  function lineLength(line) {
    if (line.height == 0) return 0;
    var len = line.text.length, merged, cur = line;
    while (merged = collapsedSpanAtStart(cur)) {
      var found = merged.find(0, true);
      cur = found.from.line;
      len += found.from.ch - found.to.ch;
    }
    cur = line;
    while (merged = collapsedSpanAtEnd(cur)) {
      var found = merged.find(0, true);
      len -= cur.text.length - found.from.ch;
      cur = found.to.line;
      len += cur.text.length - found.to.ch;
    }
    return len;
  }

  // Find the longest line in the document.
  function findMaxLine(cm) {
    var d = cm.display, doc = cm.doc;
    d.maxLine = getLine(doc, doc.first);
    d.maxLineLength = lineLength(d.maxLine);
    d.maxLineChanged = true;
    doc.iter(function(line) {
      var len = lineLength(line);
      if (len > d.maxLineLength) {
        d.maxLineLength = len;
        d.maxLine = line;
      }
    });
  }

  // Make sure the gutters options contains the element
  // "CodeMirror-linenumbers" when the lineNumbers option is true.
  function setGuttersForLineNumbers(options) {
    var found = indexOf(options.gutters, "CodeMirror-linenumbers");
    if (found == -1 && options.lineNumbers) {
      options.gutters = options.gutters.concat(["CodeMirror-linenumbers"]);
    } else if (found > -1 && !options.lineNumbers) {
      options.gutters = options.gutters.slice(0);
      options.gutters.splice(found, 1);
    }
  }

  // SCROLLBARS

  // Prepare DOM reads needed to update the scrollbars. Done in one
  // shot to minimize update/measure roundtrips.
  function measureForScrollbars(cm) {
    var d = cm.display, gutterW = d.gutters.offsetWidth;
    var docH = Math.round(cm.doc.height + paddingVert(cm.display));
    return {
      clientHeight: d.scroller.clientHeight,
      viewHeight: d.wrapper.clientHeight,
      scrollWidth: d.scroller.scrollWidth, clientWidth: d.scroller.clientWidth,
      viewWidth: d.wrapper.clientWidth,
      barLeft: cm.options.fixedGutter ? gutterW : 0,
      docHeight: docH,
      scrollHeight: docH + scrollGap(cm) + d.barHeight,
      nativeBarWidth: d.nativeBarWidth,
      gutterWidth: gutterW
    };
  }

  function NativeScrollbars(place, scroll, cm) {
    this.cm = cm;
    var vert = this.vert = elt("div", [elt("div", null, null, "min-width: 1px")], "CodeMirror-vscrollbar");
    var horiz = this.horiz = elt("div", [elt("div", null, null, "height: 100%; min-height: 1px")], "CodeMirror-hscrollbar");
    place(vert); place(horiz);

    on(vert, "scroll", function() {
      if (vert.clientHeight) scroll(vert.scrollTop, "vertical");
    });
    on(horiz, "scroll", function() {
      if (horiz.clientWidth) scroll(horiz.scrollLeft, "horizontal");
    });

    this.checkedZeroWidth = false;
    // Need to set a minimum width to see the scrollbar on IE7 (but must not set it on IE8).
    if (ie && ie_version < 8) this.horiz.style.minHeight = this.vert.style.minWidth = "18px";
  }

  NativeScrollbars.prototype = copyObj({
    update: function(measure) {
      var needsH = measure.scrollWidth > measure.clientWidth + 1;
      var needsV = measure.scrollHeight > measure.clientHeight + 1;
      var sWidth = measure.nativeBarWidth;

      if (needsV) {
        this.vert.style.display = "block";
        this.vert.style.bottom = needsH ? sWidth + "px" : "0";
        var totalHeight = measure.viewHeight - (needsH ? sWidth : 0);
        // A bug in IE8 can cause this value to be negative, so guard it.
        this.vert.firstChild.style.height =
          Math.max(0, measure.scrollHeight - measure.clientHeight + totalHeight) + "px";
      } else {
        this.vert.style.display = "";
        this.vert.firstChild.style.height = "0";
      }

      if (needsH) {
        this.horiz.style.display = "block";
        this.horiz.style.right = needsV ? sWidth + "px" : "0";
        this.horiz.style.left = measure.barLeft + "px";
        var totalWidth = measure.viewWidth - measure.barLeft - (needsV ? sWidth : 0);
        this.horiz.firstChild.style.width =
          (measure.scrollWidth - measure.clientWidth + totalWidth) + "px";
      } else {
        this.horiz.style.display = "";
        this.horiz.firstChild.style.width = "0";
      }

      if (!this.checkedZeroWidth && measure.clientHeight > 0) {
        if (sWidth == 0) this.zeroWidthHack();
        this.checkedZeroWidth = true;
      }

      return {right: needsV ? sWidth : 0, bottom: needsH ? sWidth : 0};
    },
    setScrollLeft: function(pos) {
      if (this.horiz.scrollLeft != pos) this.horiz.scrollLeft = pos;
      if (this.disableHoriz) this.enableZeroWidthBar(this.horiz, this.disableHoriz);
    },
    setScrollTop: function(pos) {
      if (this.vert.scrollTop != pos) this.vert.scrollTop = pos;
      if (this.disableVert) this.enableZeroWidthBar(this.vert, this.disableVert);
    },
    zeroWidthHack: function() {
      var w = mac && !mac_geMountainLion ? "12px" : "18px";
      this.horiz.style.height = this.vert.style.width = w;
      this.horiz.style.pointerEvents = this.vert.style.pointerEvents = "none";
      this.disableHoriz = new Delayed;
      this.disableVert = new Delayed;
    },
    enableZeroWidthBar: function(bar, delay) {
      bar.style.pointerEvents = "auto";
      function maybeDisable() {
        // To find out whether the scrollbar is still visible, we
        // check whether the element under the pixel in the bottom
        // left corner of the scrollbar box is the scrollbar box
        // itself (when the bar is still visible) or its filler child
        // (when the bar is hidden). If it is still visible, we keep
        // it enabled, if it's hidden, we disable pointer events.
        var box = bar.getBoundingClientRect();
        var elt = document.elementFromPoint(box.left + 1, box.bottom - 1);
        if (elt != bar) bar.style.pointerEvents = "none";
        else delay.set(1000, maybeDisable);
      }
      delay.set(1000, maybeDisable);
    },
    clear: function() {
      var parent = this.horiz.parentNode;
      parent.removeChild(this.horiz);
      parent.removeChild(this.vert);
    }
  }, NativeScrollbars.prototype);

  function NullScrollbars() {}

  NullScrollbars.prototype = copyObj({
    update: function() { return {bottom: 0, right: 0}; },
    setScrollLeft: function() {},
    setScrollTop: function() {},
    clear: function() {}
  }, NullScrollbars.prototype);

  CodeMirror.scrollbarModel = {"native": NativeScrollbars, "null": NullScrollbars};

  function initScrollbars(cm) {
    if (cm.display.scrollbars) {
      cm.display.scrollbars.clear();
      if (cm.display.scrollbars.addClass)
        rmClass(cm.display.wrapper, cm.display.scrollbars.addClass);
    }

    cm.display.scrollbars = new CodeMirror.scrollbarModel[cm.options.scrollbarStyle](function(node) {
      cm.display.wrapper.insertBefore(node, cm.display.scrollbarFiller);
      // Prevent clicks in the scrollbars from killing focus
      on(node, "mousedown", function() {
        if (cm.state.focused) setTimeout(function() { cm.display.input.focus(); }, 0);
      });
      node.setAttribute("cm-not-content", "true");
    }, function(pos, axis) {
      if (axis == "horizontal") setScrollLeft(cm, pos);
      else setScrollTop(cm, pos);
    }, cm);
    if (cm.display.scrollbars.addClass)
      addClass(cm.display.wrapper, cm.display.scrollbars.addClass);
  }

  function updateScrollbars(cm, measure) {
    if (!measure) measure = measureForScrollbars(cm);
    var startWidth = cm.display.barWidth, startHeight = cm.display.barHeight;
    updateScrollbarsInner(cm, measure);
    for (var i = 0; i < 4 && startWidth != cm.display.barWidth || startHeight != cm.display.barHeight; i++) {
      if (startWidth != cm.display.barWidth && cm.options.lineWrapping)
        updateHeightsInViewport(cm);
      updateScrollbarsInner(cm, measureForScrollbars(cm));
      startWidth = cm.display.barWidth; startHeight = cm.display.barHeight;
    }
  }

  // Re-synchronize the fake scrollbars with the actual size of the
  // content.
  function updateScrollbarsInner(cm, measure) {
    var d = cm.display;
    var sizes = d.scrollbars.update(measure);

    d.sizer.style.paddingRight = (d.barWidth = sizes.right) + "px";
    d.sizer.style.paddingBottom = (d.barHeight = sizes.bottom) + "px";
    d.heightForcer.style.borderBottom = sizes.bottom + "px solid transparent"

    if (sizes.right && sizes.bottom) {
      d.scrollbarFiller.style.display = "block";
      d.scrollbarFiller.style.height = sizes.bottom + "px";
      d.scrollbarFiller.style.width = sizes.right + "px";
    } else d.scrollbarFiller.style.display = "";
    if (sizes.bottom && cm.options.coverGutterNextToScrollbar && cm.options.fixedGutter) {
      d.gutterFiller.style.display = "block";
      d.gutterFiller.style.height = sizes.bottom + "px";
      d.gutterFiller.style.width = measure.gutterWidth + "px";
    } else d.gutterFiller.style.display = "";
  }

  // Compute the lines that are visible in a given viewport (defaults
  // the the current scroll position). viewport may contain top,
  // height, and ensure (see op.scrollToPos) properties.
  function visibleLines(display, doc, viewport) {
    var top = viewport && viewport.top != null ? Math.max(0, viewport.top) : display.scroller.scrollTop;
    top = Math.floor(top - paddingTop(display));
    var bottom = viewport && viewport.bottom != null ? viewport.bottom : top + display.wrapper.clientHeight;

    var from = lineAtHeight(doc, top), to = lineAtHeight(doc, bottom);
    // Ensure is a {from: {line, ch}, to: {line, ch}} object, and
    // forces those lines into the viewport (if possible).
    if (viewport && viewport.ensure) {
      var ensureFrom = viewport.ensure.from.line, ensureTo = viewport.ensure.to.line;
      if (ensureFrom < from) {
        from = ensureFrom;
        to = lineAtHeight(doc, heightAtLine(getLine(doc, ensureFrom)) + display.wrapper.clientHeight);
      } else if (Math.min(ensureTo, doc.lastLine()) >= to) {
        from = lineAtHeight(doc, heightAtLine(getLine(doc, ensureTo)) - display.wrapper.clientHeight);
        to = ensureTo;
      }
    }
    return {from: from, to: Math.max(to, from + 1)};
  }

  // LINE NUMBERS

  // Re-align line numbers and gutter marks to compensate for
  // horizontal scrolling.
  function alignHorizontally(cm) {
    var display = cm.display, view = display.view;
    if (!display.alignWidgets && (!display.gutters.firstChild || !cm.options.fixedGutter)) return;
    var comp = compensateForHScroll(display) - display.scroller.scrollLeft + cm.doc.scrollLeft;
    var gutterW = display.gutters.offsetWidth, left = comp + "px";
    for (var i = 0; i < view.length; i++) if (!view[i].hidden) {
      if (cm.options.fixedGutter && view[i].gutter)
        view[i].gutter.style.left = left;
      var align = view[i].alignable;
      if (align) for (var j = 0; j < align.length; j++)
        align[j].style.left = left;
    }
    if (cm.options.fixedGutter)
      display.gutters.style.left = (comp + gutterW) + "px";
  }

  // Used to ensure that the line number gutter is still the right
  // size for the current document size. Returns true when an update
  // is needed.
  function maybeUpdateLineNumberWidth(cm) {
    if (!cm.options.lineNumbers) return false;
    var doc = cm.doc, last = lineNumberFor(cm.options, doc.first + doc.size - 1), display = cm.display;
    if (last.length != display.lineNumChars) {
      var test = display.measure.appendChild(elt("div", [elt("div", last)],
                                                 "CodeMirror-linenumber CodeMirror-gutter-elt"));
      var innerW = test.firstChild.offsetWidth, padding = test.offsetWidth - innerW;
      display.lineGutter.style.width = "";
      display.lineNumInnerWidth = Math.max(innerW, display.lineGutter.offsetWidth - padding) + 1;
      display.lineNumWidth = display.lineNumInnerWidth + padding;
      display.lineNumChars = display.lineNumInnerWidth ? last.length : -1;
      display.lineGutter.style.width = display.lineNumWidth + "px";
      updateGutterSpace(cm);
      return true;
    }
    return false;
  }

  function lineNumberFor(options, i) {
    return String(options.lineNumberFormatter(i + options.firstLineNumber));
  }

  // Computes display.scroller.scrollLeft + display.gutters.offsetWidth,
  // but using getBoundingClientRect to get a sub-pixel-accurate
  // result.
  function compensateForHScroll(display) {
    return display.scroller.getBoundingClientRect().left - display.sizer.getBoundingClientRect().left;
  }

  // DISPLAY DRAWING

  function DisplayUpdate(cm, viewport, force) {
    var display = cm.display;

    this.viewport = viewport;
    // Store some values that we'll need later (but don't want to force a relayout for)
    this.visible = visibleLines(display, cm.doc, viewport);
    this.editorIsHidden = !display.wrapper.offsetWidth;
    this.wrapperHeight = display.wrapper.clientHeight;
    this.wrapperWidth = display.wrapper.clientWidth;
    this.oldDisplayWidth = displayWidth(cm);
    this.force = force;
    this.dims = getDimensions(cm);
    this.events = [];
  }

  DisplayUpdate.prototype.signal = function(emitter, type) {
    if (hasHandler(emitter, type))
      this.events.push(arguments);
  };
  DisplayUpdate.prototype.finish = function() {
    for (var i = 0; i < this.events.length; i++)
      signal.apply(null, this.events[i]);
  };

  function maybeClipScrollbars(cm) {
    var display = cm.display;
    if (!display.scrollbarsClipped && display.scroller.offsetWidth) {
      display.nativeBarWidth = display.scroller.offsetWidth - display.scroller.clientWidth;
      display.heightForcer.style.height = scrollGap(cm) + "px";
      display.sizer.style.marginBottom = -display.nativeBarWidth + "px";
      display.sizer.style.borderRightWidth = scrollGap(cm) + "px";
      display.scrollbarsClipped = true;
    }
  }

  // Does the actual updating of the line display. Bails out
  // (returning false) when there is nothing to be done and forced is
  // false.
  function updateDisplayIfNeeded(cm, update) {
    var display = cm.display, doc = cm.doc;

    if (update.editorIsHidden) {
      resetView(cm);
      return false;
    }

    // Bail out if the visible area is already rendered and nothing changed.
    if (!update.force &&
        update.visible.from >= display.viewFrom && update.visible.to <= display.viewTo &&
        (display.updateLineNumbers == null || display.updateLineNumbers >= display.viewTo) &&
        display.renderedView == display.view && countDirtyView(cm) == 0)
      return false;

    if (maybeUpdateLineNumberWidth(cm)) {
      resetView(cm);
      update.dims = getDimensions(cm);
    }

    // Compute a suitable new viewport (from & to)
    var end = doc.first + doc.size;
    var from = Math.max(update.visible.from - cm.options.viewportMargin, doc.first);
    var to = Math.min(end, update.visible.to + cm.options.viewportMargin);
    if (display.viewFrom < from && from - display.viewFrom < 20) from = Math.max(doc.first, display.viewFrom);
    if (display.viewTo > to && display.viewTo - to < 20) to = Math.min(end, display.viewTo);
    if (sawCollapsedSpans) {
      from = visualLineNo(cm.doc, from);
      to = visualLineEndNo(cm.doc, to);
    }

    var different = from != display.viewFrom || to != display.viewTo ||
      display.lastWrapHeight != update.wrapperHeight || display.lastWrapWidth != update.wrapperWidth;
    adjustView(cm, from, to);

    display.viewOffset = heightAtLine(getLine(cm.doc, display.viewFrom));
    // Position the mover div to align with the current scroll position
    cm.display.mover.style.top = display.viewOffset + "px";

    var toUpdate = countDirtyView(cm);
    if (!different && toUpdate == 0 && !update.force && display.renderedView == display.view &&
        (display.updateLineNumbers == null || display.updateLineNumbers >= display.viewTo))
      return false;

    // For big changes, we hide the enclosing element during the
    // update, since that speeds up the operations on most browsers.
    var focused = activeElt();
    if (toUpdate > 4) display.lineDiv.style.display = "none";
    patchDisplay(cm, display.updateLineNumbers, update.dims);
    if (toUpdate > 4) display.lineDiv.style.display = "";
    display.renderedView = display.view;
    // There might have been a widget with a focused element that got
    // hidden or updated, if so re-focus it.
    if (focused && activeElt() != focused && focused.offsetHeight) focused.focus();

    // Prevent selection and cursors from interfering with the scroll
    // width and height.
    removeChildren(display.cursorDiv);
    removeChildren(display.selectionDiv);
    display.gutters.style.height = display.sizer.style.minHeight = 0;

    if (different) {
      display.lastWrapHeight = update.wrapperHeight;
      display.lastWrapWidth = update.wrapperWidth;
      startWorker(cm, 400);
    }

    display.updateLineNumbers = null;

    return true;
  }

  function postUpdateDisplay(cm, update) {
    var viewport = update.viewport;

    for (var first = true;; first = false) {
      if (!first || !cm.options.lineWrapping || update.oldDisplayWidth == displayWidth(cm)) {
        // Clip forced viewport to actual scrollable area.
        if (viewport && viewport.top != null)
          viewport = {top: Math.min(cm.doc.height + paddingVert(cm.display) - displayHeight(cm), viewport.top)};
        // Updated line heights might result in the drawn area not
        // actually covering the viewport. Keep looping until it does.
        update.visible = visibleLines(cm.display, cm.doc, viewport);
        if (update.visible.from >= cm.display.viewFrom && update.visible.to <= cm.display.viewTo)
          break;
      }
      if (!updateDisplayIfNeeded(cm, update)) break;
      updateHeightsInViewport(cm);
      var barMeasure = measureForScrollbars(cm);
      updateSelection(cm);
      updateScrollbars(cm, barMeasure);
      setDocumentHeight(cm, barMeasure);
    }

    update.signal(cm, "update", cm);
    if (cm.display.viewFrom != cm.display.reportedViewFrom || cm.display.viewTo != cm.display.reportedViewTo) {
      update.signal(cm, "viewportChange", cm, cm.display.viewFrom, cm.display.viewTo);
      cm.display.reportedViewFrom = cm.display.viewFrom; cm.display.reportedViewTo = cm.display.viewTo;
    }
  }

  function updateDisplaySimple(cm, viewport) {
    var update = new DisplayUpdate(cm, viewport);
    if (updateDisplayIfNeeded(cm, update)) {
      updateHeightsInViewport(cm);
      postUpdateDisplay(cm, update);
      var barMeasure = measureForScrollbars(cm);
      updateSelection(cm);
      updateScrollbars(cm, barMeasure);
      setDocumentHeight(cm, barMeasure);
      update.finish();
    }
  }

  function setDocumentHeight(cm, measure) {
    cm.display.sizer.style.minHeight = measure.docHeight + "px";
    cm.display.heightForcer.style.top = measure.docHeight + "px";
    cm.display.gutters.style.height = (measure.docHeight + cm.display.barHeight + scrollGap(cm)) + "px";
  }

  // Read the actual heights of the rendered lines, and update their
  // stored heights to match.
  function updateHeightsInViewport(cm) {
    var display = cm.display;
    var prevBottom = display.lineDiv.offsetTop;
    for (var i = 0; i < display.view.length; i++) {
      var cur = display.view[i], height;
      if (cur.hidden) continue;
      if (ie && ie_version < 8) {
        var bot = cur.node.offsetTop + cur.node.offsetHeight;
        height = bot - prevBottom;
        prevBottom = bot;
      } else {
        var box = cur.node.getBoundingClientRect();
        height = box.bottom - box.top;
      }
      var diff = cur.line.height - height;
      if (height < 2) height = textHeight(display);
      if (diff > .001 || diff < -.001) {
        updateLineHeight(cur.line, height);
        updateWidgetHeight(cur.line);
        if (cur.rest) for (var j = 0; j < cur.rest.length; j++)
          updateWidgetHeight(cur.rest[j]);
      }
    }
  }

  // Read and store the height of line widgets associated with the
  // given line.
  function updateWidgetHeight(line) {
    if (line.widgets) for (var i = 0; i < line.widgets.length; ++i)
      line.widgets[i].height = line.widgets[i].node.parentNode.offsetHeight;
  }

  // Do a bulk-read of the DOM positions and sizes needed to draw the
  // view, so that we don't interleave reading and writing to the DOM.
  function getDimensions(cm) {
    var d = cm.display, left = {}, width = {};
    var gutterLeft = d.gutters.clientLeft;
    for (var n = d.gutters.firstChild, i = 0; n; n = n.nextSibling, ++i) {
      left[cm.options.gutters[i]] = n.offsetLeft + n.clientLeft + gutterLeft;
      width[cm.options.gutters[i]] = n.clientWidth;
    }
    return {fixedPos: compensateForHScroll(d),
            gutterTotalWidth: d.gutters.offsetWidth,
            gutterLeft: left,
            gutterWidth: width,
            wrapperWidth: d.wrapper.clientWidth};
  }

  // Sync the actual display DOM structure with display.view, removing
  // nodes for lines that are no longer in view, and creating the ones
  // that are not there yet, and updating the ones that are out of
  // date.
  function patchDisplay(cm, updateNumbersFrom, dims) {
    var display = cm.display, lineNumbers = cm.options.lineNumbers;
    var container = display.lineDiv, cur = container.firstChild;

    function rm(node) {
      var next = node.nextSibling;
      // Works around a throw-scroll bug in OS X Webkit
      if (webkit && mac && cm.display.currentWheelTarget == node)
        node.style.display = "none";
      else
        node.parentNode.removeChild(node);
      return next;
    }

    var view = display.view, lineN = display.viewFrom;
    // Loop over the elements in the view, syncing cur (the DOM nodes
    // in display.lineDiv) with the view as we go.
    for (var i = 0; i < view.length; i++) {
      var lineView = view[i];
      if (lineView.hidden) {
      } else if (!lineView.node || lineView.node.parentNode != container) { // Not drawn yet
        var node = buildLineElement(cm, lineView, lineN, dims);
        container.insertBefore(node, cur);
      } else { // Already drawn
        while (cur != lineView.node) cur = rm(cur);
        var updateNumber = lineNumbers && updateNumbersFrom != null &&
          updateNumbersFrom <= lineN && lineView.lineNumber;
        if (lineView.changes) {
          if (indexOf(lineView.changes, "gutter") > -1) updateNumber = false;
          updateLineForChanges(cm, lineView, lineN, dims);
        }
        if (updateNumber) {
          removeChildren(lineView.lineNumber);
          lineView.lineNumber.appendChild(document.createTextNode(lineNumberFor(cm.options, lineN)));
        }
        cur = lineView.node.nextSibling;
      }
      lineN += lineView.size;
    }
    while (cur) cur = rm(cur);
  }

  // When an aspect of a line changes, a string is added to
  // lineView.changes. This updates the relevant part of the line's
  // DOM structure.
  function updateLineForChanges(cm, lineView, lineN, dims) {
    for (var j = 0; j < lineView.changes.length; j++) {
      var type = lineView.changes[j];
      if (type == "text") updateLineText(cm, lineView);
      else if (type == "gutter") updateLineGutter(cm, lineView, lineN, dims);
      else if (type == "class") updateLineClasses(lineView);
      else if (type == "widget") updateLineWidgets(cm, lineView, dims);
    }
    lineView.changes = null;
  }

  // Lines with gutter elements, widgets or a background class need to
  // be wrapped, and have the extra elements added to the wrapper div
  function ensureLineWrapped(lineView) {
    if (lineView.node == lineView.text) {
      lineView.node = elt("div", null, null, "position: relative");
      if (lineView.text.parentNode)
        lineView.text.parentNode.replaceChild(lineView.node, lineView.text);
      lineView.node.appendChild(lineView.text);
      if (ie && ie_version < 8) lineView.node.style.zIndex = 2;
    }
    return lineView.node;
  }

  function updateLineBackground(lineView) {
    var cls = lineView.bgClass ? lineView.bgClass + " " + (lineView.line.bgClass || "") : lineView.line.bgClass;
    if (cls) cls += " CodeMirror-linebackground";
    if (lineView.background) {
      if (cls) lineView.background.className = cls;
      else { lineView.background.parentNode.removeChild(lineView.background); lineView.background = null; }
    } else if (cls) {
      var wrap = ensureLineWrapped(lineView);
      lineView.background = wrap.insertBefore(elt("div", null, cls), wrap.firstChild);
    }
  }

  // Wrapper around buildLineContent which will reuse the structure
  // in display.externalMeasured when possible.
  function getLineContent(cm, lineView) {
    var ext = cm.display.externalMeasured;
    if (ext && ext.line == lineView.line) {
      cm.display.externalMeasured = null;
      lineView.measure = ext.measure;
      return ext.built;
    }
    return buildLineContent(cm, lineView);
  }

  // Redraw the line's text. Interacts with the background and text
  // classes because the mode may output tokens that influence these
  // classes.
  function updateLineText(cm, lineView) {
    var cls = lineView.text.className;
    var built = getLineContent(cm, lineView);
    if (lineView.text == lineView.node) lineView.node = built.pre;
    lineView.text.parentNode.replaceChild(built.pre, lineView.text);
    lineView.text = built.pre;
    if (built.bgClass != lineView.bgClass || built.textClass != lineView.textClass) {
      lineView.bgClass = built.bgClass;
      lineView.textClass = built.textClass;
      updateLineClasses(lineView);
    } else if (cls) {
      lineView.text.className = cls;
    }
  }

  function updateLineClasses(lineView) {
    updateLineBackground(lineView);
    if (lineView.line.wrapClass)
      ensureLineWrapped(lineView).className = lineView.line.wrapClass;
    else if (lineView.node != lineView.text)
      lineView.node.className = "";
    var textClass = lineView.textClass ? lineView.textClass + " " + (lineView.line.textClass || "") : lineView.line.textClass;
    lineView.text.className = textClass || "";
  }

  function updateLineGutter(cm, lineView, lineN, dims) {
    if (lineView.gutter) {
      lineView.node.removeChild(lineView.gutter);
      lineView.gutter = null;
    }
    if (lineView.gutterBackground) {
      lineView.node.removeChild(lineView.gutterBackground);
      lineView.gutterBackground = null;
    }
    if (lineView.line.gutterClass) {
      var wrap = ensureLineWrapped(lineView);
      lineView.gutterBackground = elt("div", null, "CodeMirror-gutter-background " + lineView.line.gutterClass,
                                      "left: " + (cm.options.fixedGutter ? dims.fixedPos : -dims.gutterTotalWidth) +
                                      "px; width: " + dims.gutterTotalWidth + "px");
      wrap.insertBefore(lineView.gutterBackground, lineView.text);
    }
    var markers = lineView.line.gutterMarkers;
    if (cm.options.lineNumbers || markers) {
      var wrap = ensureLineWrapped(lineView);
      var gutterWrap = lineView.gutter = elt("div", null, "CodeMirror-gutter-wrapper", "left: " +
                                             (cm.options.fixedGutter ? dims.fixedPos : -dims.gutterTotalWidth) + "px");
      cm.display.input.setUneditable(gutterWrap);
      wrap.insertBefore(gutterWrap, lineView.text);
      if (lineView.line.gutterClass)
        gutterWrap.className += " " + lineView.line.gutterClass;
      if (cm.options.lineNumbers && (!markers || !markers["CodeMirror-linenumbers"]))
        lineView.lineNumber = gutterWrap.appendChild(
          elt("div", lineNumberFor(cm.options, lineN),
              "CodeMirror-linenumber CodeMirror-gutter-elt",
              "left: " + dims.gutterLeft["CodeMirror-linenumbers"] + "px; width: "
              + cm.display.lineNumInnerWidth + "px"));
      if (markers) for (var k = 0; k < cm.options.gutters.length; ++k) {
        var id = cm.options.gutters[k], found = markers.hasOwnProperty(id) && markers[id];
        if (found)
          gutterWrap.appendChild(elt("div", [found], "CodeMirror-gutter-elt", "left: " +
                                     dims.gutterLeft[id] + "px; width: " + dims.gutterWidth[id] + "px"));
      }
    }
  }

  function updateLineWidgets(cm, lineView, dims) {
    if (lineView.alignable) lineView.alignable = null;
    for (var node = lineView.node.firstChild, next; node; node = next) {
      var next = node.nextSibling;
      if (node.className == "CodeMirror-linewidget")
        lineView.node.removeChild(node);
    }
    insertLineWidgets(cm, lineView, dims);
  }

  // Build a line's DOM representation from scratch
  function buildLineElement(cm, lineView, lineN, dims) {
    var built = getLineContent(cm, lineView);
    lineView.text = lineView.node = built.pre;
    if (built.bgClass) lineView.bgClass = built.bgClass;
    if (built.textClass) lineView.textClass = built.textClass;

    updateLineClasses(lineView);
    updateLineGutter(cm, lineView, lineN, dims);
    insertLineWidgets(cm, lineView, dims);
    return lineView.node;
  }

  // A lineView may contain multiple logical lines (when merged by
  // collapsed spans). The widgets for all of them need to be drawn.
  function insertLineWidgets(cm, lineView, dims) {
    insertLineWidgetsFor(cm, lineView.line, lineView, dims, true);
    if (lineView.rest) for (var i = 0; i < lineView.rest.length; i++)
      insertLineWidgetsFor(cm, lineView.rest[i], lineView, dims, false);
  }

  function insertLineWidgetsFor(cm, line, lineView, dims, allowAbove) {
    if (!line.widgets) return;
    var wrap = ensureLineWrapped(lineView);
    for (var i = 0, ws = line.widgets; i < ws.length; ++i) {
      var widget = ws[i], node = elt("div", [widget.node], "CodeMirror-linewidget");
      if (!widget.handleMouseEvents) node.setAttribute("cm-ignore-events", "true");
      positionLineWidget(widget, node, lineView, dims);
      cm.display.input.setUneditable(node);
      if (allowAbove && widget.above)
        wrap.insertBefore(node, lineView.gutter || lineView.text);
      else
        wrap.appendChild(node);
      signalLater(widget, "redraw");
    }
  }

  function positionLineWidget(widget, node, lineView, dims) {
    if (widget.noHScroll) {
      (lineView.alignable || (lineView.alignable = [])).push(node);
      var width = dims.wrapperWidth;
      node.style.left = dims.fixedPos + "px";
      if (!widget.coverGutter) {
        width -= dims.gutterTotalWidth;
        node.style.paddingLeft = dims.gutterTotalWidth + "px";
      }
      node.style.width = width + "px";
    }
    if (widget.coverGutter) {
      node.style.zIndex = 5;
      node.style.position = "relative";
      if (!widget.noHScroll) node.style.marginLeft = -dims.gutterTotalWidth + "px";
    }
  }

  // POSITION OBJECT

  // A Pos instance represents a position within the text.
  var Pos = CodeMirror.Pos = function(line, ch) {
    if (!(this instanceof Pos)) return new Pos(line, ch);
    this.line = line; this.ch = ch;
  };

  // Compare two positions, return 0 if they are the same, a negative
  // number when a is less, and a positive number otherwise.
  var cmp = CodeMirror.cmpPos = function(a, b) { return a.line - b.line || a.ch - b.ch; };

  function copyPos(x) {return Pos(x.line, x.ch);}
  function maxPos(a, b) { return cmp(a, b) < 0 ? b : a; }
  function minPos(a, b) { return cmp(a, b) < 0 ? a : b; }

  // INPUT HANDLING

  function ensureFocus(cm) {
    if (!cm.state.focused) { cm.display.input.focus(); onFocus(cm); }
  }

  // This will be set to a {lineWise: bool, text: [string]} object, so
  // that, when pasting, we know what kind of selections the copied
  // text was made out of.
  var lastCopied = null;

  function applyTextInput(cm, inserted, deleted, sel, origin) {
    var doc = cm.doc;
    cm.display.shift = false;
    if (!sel) sel = doc.sel;

    var paste = cm.state.pasteIncoming || origin == "paste";
    var textLines = doc.splitLines(inserted), multiPaste = null
    // When pasing N lines into N selections, insert one line per selection
    if (paste && sel.ranges.length > 1) {
      if (lastCopied && lastCopied.text.join("\n") == inserted) {
        if (sel.ranges.length % lastCopied.text.length == 0) {
          multiPaste = [];
          for (var i = 0; i < lastCopied.text.length; i++)
            multiPaste.push(doc.splitLines(lastCopied.text[i]));
        }
      } else if (textLines.length == sel.ranges.length) {
        multiPaste = map(textLines, function(l) { return [l]; });
      }
    }

    // Normal behavior is to insert the new text into every selection
    for (var i = sel.ranges.length - 1; i >= 0; i--) {
      var range = sel.ranges[i];
      var from = range.from(), to = range.to();
      if (range.empty()) {
        if (deleted && deleted > 0) // Handle deletion
          from = Pos(from.line, from.ch - deleted);
        else if (cm.state.overwrite && !paste) // Handle overwrite
          to = Pos(to.line, Math.min(getLine(doc, to.line).text.length, to.ch + lst(textLines).length));
        else if (lastCopied && lastCopied.lineWise && lastCopied.text.join("\n") == inserted)
          from = to = Pos(from.line, 0)
      }
      var updateInput = cm.curOp.updateInput;
      var changeEvent = {from: from, to: to, text: multiPaste ? multiPaste[i % multiPaste.length] : textLines,
                         origin: origin || (paste ? "paste" : cm.state.cutIncoming ? "cut" : "+input")};
      makeChange(cm.doc, changeEvent);
      signalLater(cm, "inputRead", cm, changeEvent);
    }
    if (inserted && !paste)
      triggerElectric(cm, inserted);

    ensureCursorVisible(cm);
    cm.curOp.updateInput = updateInput;
    cm.curOp.typing = true;
    cm.state.pasteIncoming = cm.state.cutIncoming = false;
  }

  function handlePaste(e, cm) {
    var pasted = e.clipboardData && e.clipboardData.getData("text/plain");
    if (pasted) {
      e.preventDefault();
      if (!cm.isReadOnly() && !cm.options.disableInput)
        runInOp(cm, function() { applyTextInput(cm, pasted, 0, null, "paste"); });
      return true;
    }
  }

  function triggerElectric(cm, inserted) {
    // When an 'electric' character is inserted, immediately trigger a reindent
    if (!cm.options.electricChars || !cm.options.smartIndent) return;
    var sel = cm.doc.sel;

    for (var i = sel.ranges.length - 1; i >= 0; i--) {
      var range = sel.ranges[i];
      if (range.head.ch > 100 || (i && sel.ranges[i - 1].head.line == range.head.line)) continue;
      var mode = cm.getModeAt(range.head);
      var indented = false;
      if (mode.electricChars) {
        for (var j = 0; j < mode.electricChars.length; j++)
          if (inserted.indexOf(mode.electricChars.charAt(j)) > -1) {
            indented = indentLine(cm, range.head.line, "smart");
            break;
          }
      } else if (mode.electricInput) {
        if (mode.electricInput.test(getLine(cm.doc, range.head.line).text.slice(0, range.head.ch)))
          indented = indentLine(cm, range.head.line, "smart");
      }
      if (indented) signalLater(cm, "electricInput", cm, range.head.line);
    }
  }

  function copyableRanges(cm) {
    var text = [], ranges = [];
    for (var i = 0; i < cm.doc.sel.ranges.length; i++) {
      var line = cm.doc.sel.ranges[i].head.line;
      var lineRange = {anchor: Pos(line, 0), head: Pos(line + 1, 0)};
      ranges.push(lineRange);
      text.push(cm.getRange(lineRange.anchor, lineRange.head));
    }
    return {text: text, ranges: ranges};
  }

  function disableBrowserMagic(field) {
    field.setAttribute("autocorrect", "off");
    field.setAttribute("autocapitalize", "off");
    field.setAttribute("spellcheck", "false");
  }

  // TEXTAREA INPUT STYLE

  function TextareaInput(cm) {
    this.cm = cm;
    // See input.poll and input.reset
    this.prevInput = "";

    // Flag that indicates whether we expect input to appear real soon
    // now (after some event like 'keypress' or 'input') and are
    // polling intensively.
    this.pollingFast = false;
    // Self-resetting timeout for the poller
    this.polling = new Delayed();
    // Tracks when input.reset has punted to just putting a short
    // string into the textarea instead of the full selection.
    this.inaccurateSelection = false;
    // Used to work around IE issue with selection being forgotten when focus moves away from textarea
    this.hasSelection = false;
    this.composing = null;
  };

  function hiddenTextarea() {
    var te = elt("textarea", null, null, "position: absolute; padding: 0; width: 1px; height: 1em; outline: none");
    var div = elt("div", [te], null, "overflow: hidden; position: relative; width: 3px; height: 0px;");
    // The textarea is kept positioned near the cursor to prevent the
    // fact that it'll be scrolled into view on input from scrolling
    // our fake cursor out of view. On webkit, when wrap=off, paste is
    // very slow. So make the area wide instead.
    if (webkit) te.style.width = "1000px";
    else te.setAttribute("wrap", "off");
    // If border: 0; -- iOS fails to open keyboard (issue #1287)
    if (ios) te.style.border = "1px solid black";
    disableBrowserMagic(te);
    return div;
  }

  TextareaInput.prototype = copyObj({
    init: function(display) {
      var input = this, cm = this.cm;

      // Wraps and hides input textarea
      var div = this.wrapper = hiddenTextarea();
      // The semihidden textarea that is focused when the editor is
      // focused, and receives input.
      var te = this.textarea = div.firstChild;
      display.wrapper.insertBefore(div, display.wrapper.firstChild);

      // Needed to hide big blue blinking cursor on Mobile Safari (doesn't seem to work in iOS 8 anymore)
      if (ios) te.style.width = "0px";

      on(te, "input", function() {
        if (ie && ie_version >= 9 && input.hasSelection) input.hasSelection = null;
        input.poll();
      });

      on(te, "paste", function(e) {
        if (signalDOMEvent(cm, e) || handlePaste(e, cm)) return

        cm.state.pasteIncoming = true;
        input.fastPoll();
      });

      function prepareCopyCut(e) {
        if (signalDOMEvent(cm, e)) return
        if (cm.somethingSelected()) {
          lastCopied = {lineWise: false, text: cm.getSelections()};
          if (input.inaccurateSelection) {
            input.prevInput = "";
            input.inaccurateSelection = false;
            te.value = lastCopied.text.join("\n");
            selectInput(te);
          }
        } else if (!cm.options.lineWiseCopyCut) {
          return;
        } else {
          var ranges = copyableRanges(cm);
          lastCopied = {lineWise: true, text: ranges.text};
          if (e.type == "cut") {
            cm.setSelections(ranges.ranges, null, sel_dontScroll);
          } else {
            input.prevInput = "";
            te.value = ranges.text.join("\n");
            selectInput(te);
          }
        }
        if (e.type == "cut") cm.state.cutIncoming = true;
      }
      on(te, "cut", prepareCopyCut);
      on(te, "copy", prepareCopyCut);

      on(display.scroller, "paste", function(e) {
        if (eventInWidget(display, e) || signalDOMEvent(cm, e)) return;
        cm.state.pasteIncoming = true;
        input.focus();
      });

      // Prevent normal selection in the editor (we handle our own)
      on(display.lineSpace, "selectstart", function(e) {
        if (!eventInWidget(display, e)) e_preventDefault(e);
      });

      on(te, "compositionstart", function() {
        var start = cm.getCursor("from");
        if (input.composing) input.composing.range.clear()
        input.composing = {
          start: start,
          range: cm.markText(start, cm.getCursor("to"), {className: "CodeMirror-composing"})
        };
      });
      on(te, "compositionend", function() {
        if (input.composing) {
          input.poll();
          input.composing.range.clear();
          input.composing = null;
        }
      });
    },

    prepareSelection: function() {
      // Redraw the selection and/or cursor
      var cm = this.cm, display = cm.display, doc = cm.doc;
      var result = prepareSelection(cm);

      // Move the hidden textarea near the cursor to prevent scrolling artifacts
      if (cm.options.moveInputWithCursor) {
        var headPos = cursorCoords(cm, doc.sel.primary().head, "div");
        var wrapOff = display.wrapper.getBoundingClientRect(), lineOff = display.lineDiv.getBoundingClientRect();
        result.teTop = Math.max(0, Math.min(display.wrapper.clientHeight - 10,
                                            headPos.top + lineOff.top - wrapOff.top));
        result.teLeft = Math.max(0, Math.min(display.wrapper.clientWidth - 10,
                                             headPos.left + lineOff.left - wrapOff.left));
      }

      return result;
    },

    showSelection: function(drawn) {
      var cm = this.cm, display = cm.display;
      removeChildrenAndAdd(display.cursorDiv, drawn.cursors);
      removeChildrenAndAdd(display.selectionDiv, drawn.selection);
      if (drawn.teTop != null) {
        this.wrapper.style.top = drawn.teTop + "px";
        this.wrapper.style.left = drawn.teLeft + "px";
      }
    },

    // Reset the input to correspond to the selection (or to be empty,
    // when not typing and nothing is selected)
    reset: function(typing) {
      if (this.contextMenuPending) return;
      var minimal, selected, cm = this.cm, doc = cm.doc;
      if (cm.somethingSelected()) {
        this.prevInput = "";
        var range = doc.sel.primary();
        minimal = hasCopyEvent &&
          (range.to().line - range.from().line > 100 || (selected = cm.getSelection()).length > 1000);
        var content = minimal ? "-" : selected || cm.getSelection();
        this.textarea.value = content;
        if (cm.state.focused) selectInput(this.textarea);
        if (ie && ie_version >= 9) this.hasSelection = content;
      } else if (!typing) {
        this.prevInput = this.textarea.value = "";
        if (ie && ie_version >= 9) this.hasSelection = null;
      }
      this.inaccurateSelection = minimal;
    },

    getField: function() { return this.textarea; },

    supportsTouch: function() { return false; },

    focus: function() {
      if (this.cm.options.readOnly != "nocursor" && (!mobile || activeElt() != this.textarea)) {
        try { this.textarea.focus(); }
        catch (e) {} // IE8 will throw if the textarea is display: none or not in DOM
      }
    },

    blur: function() { this.textarea.blur(); },

    resetPosition: function() {
      this.wrapper.style.top = this.wrapper.style.left = 0;
    },

    receivedFocus: function() { this.slowPoll(); },

    // Poll for input changes, using the normal rate of polling. This
    // runs as long as the editor is focused.
    slowPoll: function() {
      var input = this;
      if (input.pollingFast) return;
      input.polling.set(this.cm.options.pollInterval, function() {
        input.poll();
        if (input.cm.state.focused) input.slowPoll();
      });
    },

    // When an event has just come in that is likely to add or change
    // something in the input textarea, we poll faster, to ensure that
    // the change appears on the screen quickly.
    fastPoll: function() {
      var missed = false, input = this;
      input.pollingFast = true;
      function p() {
        var changed = input.poll();
        if (!changed && !missed) {missed = true; input.polling.set(60, p);}
        else {input.pollingFast = false; input.slowPoll();}
      }
      input.polling.set(20, p);
    },

    // Read input from the textarea, and update the document to match.
    // When something is selected, it is present in the textarea, and
    // selected (unless it is huge, in which case a placeholder is
    // used). When nothing is selected, the cursor sits after previously
    // seen text (can be empty), which is stored in prevInput (we must
    // not reset the textarea when typing, because that breaks IME).
    poll: function() {
      var cm = this.cm, input = this.textarea, prevInput = this.prevInput;
      // Since this is called a *lot*, try to bail out as cheaply as
      // possible when it is clear that nothing happened. hasSelection
      // will be the case when there is a lot of text in the textarea,
      // in which case reading its value would be expensive.
      if (this.contextMenuPending || !cm.state.focused ||
          (hasSelection(input) && !prevInput && !this.composing) ||
          cm.isReadOnly() || cm.options.disableInput || cm.state.keySeq)
        return false;

      var text = input.value;
      // If nothing changed, bail.
      if (text == prevInput && !cm.somethingSelected()) return false;
      // Work around nonsensical selection resetting in IE9/10, and
      // inexplicable appearance of private area unicode characters on
      // some key combos in Mac (#2689).
      if (ie && ie_version >= 9 && this.hasSelection === text ||
          mac && /[\uf700-\uf7ff]/.test(text)) {
        cm.display.input.reset();
        return false;
      }

      if (cm.doc.sel == cm.display.selForContextMenu) {
        var first = text.charCodeAt(0);
        if (first == 0x200b && !prevInput) prevInput = "\u200b";
        if (first == 0x21da) { this.reset(); return this.cm.execCommand("undo"); }
      }
      // Find the part of the input that is actually new
      var same = 0, l = Math.min(prevInput.length, text.length);
      while (same < l && prevInput.charCodeAt(same) == text.charCodeAt(same)) ++same;

      var self = this;
      runInOp(cm, function() {
        applyTextInput(cm, text.slice(same), prevInput.length - same,
                       null, self.composing ? "*compose" : null);

        // Don't leave long text in the textarea, since it makes further polling slow
        if (text.length > 1000 || text.indexOf("\n") > -1) input.value = self.prevInput = "";
        else self.prevInput = text;

        if (self.composing) {
          self.composing.range.clear();
          self.composing.range = cm.markText(self.composing.start, cm.getCursor("to"),
                                             {className: "CodeMirror-composing"});
        }
      });
      return true;
    },

    ensurePolled: function() {
      if (this.pollingFast && this.poll()) this.pollingFast = false;
    },

    onKeyPress: function() {
      if (ie && ie_version >= 9) this.hasSelection = null;
      this.fastPoll();
    },

    onContextMenu: function(e) {
      var input = this, cm = input.cm, display = cm.display, te = input.textarea;
      var pos = posFromMouse(cm, e), scrollPos = display.scroller.scrollTop;
      if (!pos || presto) return; // Opera is difficult.

      // Reset the current text selection only if the click is done outside of the selection
      // and 'resetSelectionOnContextMenu' option is true.
      var reset = cm.options.resetSelectionOnContextMenu;
      if (reset && cm.doc.sel.contains(pos) == -1)
        operation(cm, setSelection)(cm.doc, simpleSelection(pos), sel_dontScroll);

      var oldCSS = te.style.cssText, oldWrapperCSS = input.wrapper.style.cssText;
      input.wrapper.style.cssText = "position: absolute"
      var wrapperBox = input.wrapper.getBoundingClientRect()
      te.style.cssText = "position: absolute; width: 30px; height: 30px; top: " + (e.clientY - wrapperBox.top - 5) +
        "px; left: " + (e.clientX - wrapperBox.left - 5) + "px; z-index: 1000; background: " +
        (ie ? "rgba(255, 255, 255, .05)" : "transparent") +
        "; outline: none; border-width: 0; outline: none; overflow: hidden; opacity: .05; filter: alpha(opacity=5);";
      if (webkit) var oldScrollY = window.scrollY; // Work around Chrome issue (#2712)
      display.input.focus();
      if (webkit) window.scrollTo(null, oldScrollY);
      display.input.reset();
      // Adds "Select all" to context menu in FF
      if (!cm.somethingSelected()) te.value = input.prevInput = " ";
      input.contextMenuPending = true;
      display.selForContextMenu = cm.doc.sel;
      clearTimeout(display.detectingSelectAll);

      // Select-all will be greyed out if there's nothing to select, so
      // this adds a zero-width space so that we can later check whether
      // it got selected.
      function prepareSelectAllHack() {
        if (te.selectionStart != null) {
          var selected = cm.somethingSelected();
          var extval = "\u200b" + (selected ? te.value : "");
          te.value = "\u21da"; // Used to catch context-menu undo
          te.value = extval;
          input.prevInput = selected ? "" : "\u200b";
          te.selectionStart = 1; te.selectionEnd = extval.length;
          // Re-set this, in case some other handler touched the
          // selection in the meantime.
          display.selForContextMenu = cm.doc.sel;
        }
      }
      function rehide() {
        input.contextMenuPending = false;
        input.wrapper.style.cssText = oldWrapperCSS
        te.style.cssText = oldCSS;
        if (ie && ie_version < 9) display.scrollbars.setScrollTop(display.scroller.scrollTop = scrollPos);

        // Try to detect the user choosing select-all
        if (te.selectionStart != null) {
          if (!ie || (ie && ie_version < 9)) prepareSelectAllHack();
          var i = 0, poll = function() {
            if (display.selForContextMenu == cm.doc.sel && te.selectionStart == 0 &&
                te.selectionEnd > 0 && input.prevInput == "\u200b")
              operation(cm, commands.selectAll)(cm);
            else if (i++ < 10) display.detectingSelectAll = setTimeout(poll, 500);
            else display.input.reset();
          };
          display.detectingSelectAll = setTimeout(poll, 200);
        }
      }

      if (ie && ie_version >= 9) prepareSelectAllHack();
      if (captureRightClick) {
        e_stop(e);
        var mouseup = function() {
          off(window, "mouseup", mouseup);
          setTimeout(rehide, 20);
        };
        on(window, "mouseup", mouseup);
      } else {
        setTimeout(rehide, 50);
      }
    },

    readOnlyChanged: function(val) {
      if (!val) this.reset();
    },

    setUneditable: nothing,

    needsContentAttribute: false
  }, TextareaInput.prototype);

  // CONTENTEDITABLE INPUT STYLE

  function ContentEditableInput(cm) {
    this.cm = cm;
    this.lastAnchorNode = this.lastAnchorOffset = this.lastFocusNode = this.lastFocusOffset = null;
    this.polling = new Delayed();
    this.gracePeriod = false;
  }

  ContentEditableInput.prototype = copyObj({
    init: function(display) {
      var input = this, cm = input.cm;
      var div = input.div = display.lineDiv;
      disableBrowserMagic(div);

      on(div, "paste", function(e) {
        if (!signalDOMEvent(cm, e)) handlePaste(e, cm);
      })

      on(div, "compositionstart", function(e) {
        var data = e.data;
        input.composing = {sel: cm.doc.sel, data: data, startData: data};
        if (!data) return;
        var prim = cm.doc.sel.primary();
        var line = cm.getLine(prim.head.line);
        var found = line.indexOf(data, Math.max(0, prim.head.ch - data.length));
        if (found > -1 && found <= prim.head.ch)
          input.composing.sel = simpleSelection(Pos(prim.head.line, found),
                                                Pos(prim.head.line, found + data.length));
      });
      on(div, "compositionupdate", function(e) {
        input.composing.data = e.data;
      });
      on(div, "compositionend", function(e) {
        var ours = input.composing;
        if (!ours) return;
        if (e.data != ours.startData && !/\u200b/.test(e.data))
          ours.data = e.data;
        // Need a small delay to prevent other code (input event,
        // selection polling) from doing damage when fired right after
        // compositionend.
        setTimeout(function() {
          if (!ours.handled)
            input.applyComposition(ours);
          if (input.composing == ours)
            input.composing = null;
        }, 50);
      });

      on(div, "touchstart", function() {
        input.forceCompositionEnd();
      });

      on(div, "input", function() {
        if (input.composing) return;
        if (cm.isReadOnly() || !input.pollContent())
          runInOp(input.cm, function() {regChange(cm);});
      });

      function onCopyCut(e) {
        if (signalDOMEvent(cm, e)) return
        if (cm.somethingSelected()) {
          lastCopied = {lineWise: false, text: cm.getSelections()};
          if (e.type == "cut") cm.replaceSelection("", null, "cut");
        } else if (!cm.options.lineWiseCopyCut) {
          return;
        } else {
          var ranges = copyableRanges(cm);
          lastCopied = {lineWise: true, text: ranges.text};
          if (e.type == "cut") {
            cm.operation(function() {
              cm.setSelections(ranges.ranges, 0, sel_dontScroll);
              cm.replaceSelection("", null, "cut");
            });
          }
        }
        // iOS exposes the clipboard API, but seems to discard content inserted into it
        if (e.clipboardData && !ios) {
          e.preventDefault();
          e.clipboardData.clearData();
          e.clipboardData.setData("text/plain", lastCopied.text.join("\n"));
        } else {
          // Old-fashioned briefly-focus-a-textarea hack
          var kludge = hiddenTextarea(), te = kludge.firstChild;
          cm.display.lineSpace.insertBefore(kludge, cm.display.lineSpace.firstChild);
          te.value = lastCopied.text.join("\n");
          var hadFocus = document.activeElement;
          selectInput(te);
          setTimeout(function() {
            cm.display.lineSpace.removeChild(kludge);
            hadFocus.focus();
          }, 50);
        }
      }
      on(div, "copy", onCopyCut);
      on(div, "cut", onCopyCut);
    },

    prepareSelection: function() {
      var result = prepareSelection(this.cm, false);
      result.focus = this.cm.state.focused;
      return result;
    },

    showSelection: function(info, takeFocus) {
      if (!info || !this.cm.display.view.length) return;
      if (info.focus || takeFocus) this.showPrimarySelection();
      this.showMultipleSelections(info);
    },

    showPrimarySelection: function() {
      var sel = window.getSelection(), prim = this.cm.doc.sel.primary();
      var curAnchor = domToPos(this.cm, sel.anchorNode, sel.anchorOffset);
      var curFocus = domToPos(this.cm, sel.focusNode, sel.focusOffset);
      if (curAnchor && !curAnchor.bad && curFocus && !curFocus.bad &&
          cmp(minPos(curAnchor, curFocus), prim.from()) == 0 &&
          cmp(maxPos(curAnchor, curFocus), prim.to()) == 0)
        return;

      var start = posToDOM(this.cm, prim.from());
      var end = posToDOM(this.cm, prim.to());
      if (!start && !end) return;

      var view = this.cm.display.view;
      var old = sel.rangeCount && sel.getRangeAt(0);
      if (!start) {
        start = {node: view[0].measure.map[2], offset: 0};
      } else if (!end) { // FIXME dangerously hacky
        var measure = view[view.length - 1].measure;
        var map = measure.maps ? measure.maps[measure.maps.length - 1] : measure.map;
        end = {node: map[map.length - 1], offset: map[map.length - 2] - map[map.length - 3]};
      }

      try { var rng = range(start.node, start.offset, end.offset, end.node); }
      catch(e) {} // Our model of the DOM might be outdated, in which case the range we try to set can be impossible
      if (rng) {
        if (!gecko && this.cm.state.focused) {
          sel.collapse(start.node, start.offset);
          if (!rng.collapsed) sel.addRange(rng);
        } else {
          sel.removeAllRanges();
          sel.addRange(rng);
        }
        if (old && sel.anchorNode == null) sel.addRange(old);
        else if (gecko) this.startGracePeriod();
      }
      this.rememberSelection();
    },

    startGracePeriod: function() {
      var input = this;
      clearTimeout(this.gracePeriod);
      this.gracePeriod = setTimeout(function() {
        input.gracePeriod = false;
        if (input.selectionChanged())
          input.cm.operation(function() { input.cm.curOp.selectionChanged = true; });
      }, 20);
    },

    showMultipleSelections: function(info) {
      removeChildrenAndAdd(this.cm.display.cursorDiv, info.cursors);
      removeChildrenAndAdd(this.cm.display.selectionDiv, info.selection);
    },

    rememberSelection: function() {
      var sel = window.getSelection();
      this.lastAnchorNode = sel.anchorNode; this.lastAnchorOffset = sel.anchorOffset;
      this.lastFocusNode = sel.focusNode; this.lastFocusOffset = sel.focusOffset;
    },

    selectionInEditor: function() {
      var sel = window.getSelection();
      if (!sel.rangeCount) return false;
      var node = sel.getRangeAt(0).commonAncestorContainer;
      return contains(this.div, node);
    },

    focus: function() {
      if (this.cm.options.readOnly != "nocursor") this.div.focus();
    },
    blur: function() { this.div.blur(); },
    getField: function() { return this.div; },

    supportsTouch: function() { return true; },

    receivedFocus: function() {
      var input = this;
      if (this.selectionInEditor())
        this.pollSelection();
      else
        runInOp(this.cm, function() { input.cm.curOp.selectionChanged = true; });

      function poll() {
        if (input.cm.state.focused) {
          input.pollSelection();
          input.polling.set(input.cm.options.pollInterval, poll);
        }
      }
      this.polling.set(this.cm.options.pollInterval, poll);
    },

    selectionChanged: function() {
      var sel = window.getSelection();
      return sel.anchorNode != this.lastAnchorNode || sel.anchorOffset != this.lastAnchorOffset ||
        sel.focusNode != this.lastFocusNode || sel.focusOffset != this.lastFocusOffset;
    },

    pollSelection: function() {
      if (!this.composing && !this.gracePeriod && this.selectionChanged()) {
        var sel = window.getSelection(), cm = this.cm;
        this.rememberSelection();
        var anchor = domToPos(cm, sel.anchorNode, sel.anchorOffset);
        var head = domToPos(cm, sel.focusNode, sel.focusOffset);
        if (anchor && head) runInOp(cm, function() {
          setSelection(cm.doc, simpleSelection(anchor, head), sel_dontScroll);
          if (anchor.bad || head.bad) cm.curOp.selectionChanged = true;
        });
      }
    },

    pollContent: function() {
      var cm = this.cm, display = cm.display, sel = cm.doc.sel.primary();
      var from = sel.from(), to = sel.to();
      if (from.line < display.viewFrom || to.line > display.viewTo - 1) return false;

      var fromIndex;
      if (from.line == display.viewFrom || (fromIndex = findViewIndex(cm, from.line)) == 0) {
        var fromLine = lineNo(display.view[0].line);
        var fromNode = display.view[0].node;
      } else {
        var fromLine = lineNo(display.view[fromIndex].line);
        var fromNode = display.view[fromIndex - 1].node.nextSibling;
      }
      var toIndex = findViewIndex(cm, to.line);
      if (toIndex == display.view.length - 1) {
        var toLine = display.viewTo - 1;
        var toNode = display.lineDiv.lastChild;
      } else {
        var toLine = lineNo(display.view[toIndex + 1].line) - 1;
        var toNode = display.view[toIndex + 1].node.previousSibling;
      }

      var newText = cm.doc.splitLines(domTextBetween(cm, fromNode, toNode, fromLine, toLine));
      var oldText = getBetween(cm.doc, Pos(fromLine, 0), Pos(toLine, getLine(cm.doc, toLine).text.length));
      while (newText.length > 1 && oldText.length > 1) {
        if (lst(newText) == lst(oldText)) { newText.pop(); oldText.pop(); toLine--; }
        else if (newText[0] == oldText[0]) { newText.shift(); oldText.shift(); fromLine++; }
        else break;
      }

      var cutFront = 0, cutEnd = 0;
      var newTop = newText[0], oldTop = oldText[0], maxCutFront = Math.min(newTop.length, oldTop.length);
      while (cutFront < maxCutFront && newTop.charCodeAt(cutFront) == oldTop.charCodeAt(cutFront))
        ++cutFront;
      var newBot = lst(newText), oldBot = lst(oldText);
      var maxCutEnd = Math.min(newBot.length - (newText.length == 1 ? cutFront : 0),
                               oldBot.length - (oldText.length == 1 ? cutFront : 0));
      while (cutEnd < maxCutEnd &&
             newBot.charCodeAt(newBot.length - cutEnd - 1) == oldBot.charCodeAt(oldBot.length - cutEnd - 1))
        ++cutEnd;

      newText[newText.length - 1] = newBot.slice(0, newBot.length - cutEnd);
      newText[0] = newText[0].slice(cutFront);

      var chFrom = Pos(fromLine, cutFront);
      var chTo = Pos(toLine, oldText.length ? lst(oldText).length - cutEnd : 0);
      if (newText.length > 1 || newText[0] || cmp(chFrom, chTo)) {
        replaceRange(cm.doc, newText, chFrom, chTo, "+input");
        return true;
      }
    },

    ensurePolled: function() {
      this.forceCompositionEnd();
    },
    reset: function() {
      this.forceCompositionEnd();
    },
    forceCompositionEnd: function() {
      if (!this.composing || this.composing.handled) return;
      this.applyComposition(this.composing);
      this.composing.handled = true;
      this.div.blur();
      this.div.focus();
    },
    applyComposition: function(composing) {
      if (this.cm.isReadOnly())
        operation(this.cm, regChange)(this.cm)
      else if (composing.data && composing.data != composing.startData)
        operation(this.cm, applyTextInput)(this.cm, composing.data, 0, composing.sel);
    },

    setUneditable: function(node) {
      node.contentEditable = "false"
    },

    onKeyPress: function(e) {
      e.preventDefault();
      if (!this.cm.isReadOnly())
        operation(this.cm, applyTextInput)(this.cm, String.fromCharCode(e.charCode == null ? e.keyCode : e.charCode), 0);
    },

    readOnlyChanged: function(val) {
      this.div.contentEditable = String(val != "nocursor")
    },

    onContextMenu: nothing,
    resetPosition: nothing,

    needsContentAttribute: true
  }, ContentEditableInput.prototype);

  function posToDOM(cm, pos) {
    var view = findViewForLine(cm, pos.line);
    if (!view || view.hidden) return null;
    var line = getLine(cm.doc, pos.line);
    var info = mapFromLineView(view, line, pos.line);

    var order = getOrder(line), side = "left";
    if (order) {
      var partPos = getBidiPartAt(order, pos.ch);
      side = partPos % 2 ? "right" : "left";
    }
    var result = nodeAndOffsetInLineMap(info.map, pos.ch, side);
    result.offset = result.collapse == "right" ? result.end : result.start;
    return result;
  }

  function badPos(pos, bad) { if (bad) pos.bad = true; return pos; }

  function domToPos(cm, node, offset) {
    var lineNode;
    if (node == cm.display.lineDiv) {
      lineNode = cm.display.lineDiv.childNodes[offset];
      if (!lineNode) return badPos(cm.clipPos(Pos(cm.display.viewTo - 1)), true);
      node = null; offset = 0;
    } else {
      for (lineNode = node;; lineNode = lineNode.parentNode) {
        if (!lineNode || lineNode == cm.display.lineDiv) return null;
        if (lineNode.parentNode && lineNode.parentNode == cm.display.lineDiv) break;
      }
    }
    for (var i = 0; i < cm.display.view.length; i++) {
      var lineView = cm.display.view[i];
      if (lineView.node == lineNode)
        return locateNodeInLineView(lineView, node, offset);
    }
  }

  function locateNodeInLineView(lineView, node, offset) {
    var wrapper = lineView.text.firstChild, bad = false;
    if (!node || !contains(wrapper, node)) return badPos(Pos(lineNo(lineView.line), 0), true);
    if (node == wrapper) {
      bad = true;
      node = wrapper.childNodes[offset];
      offset = 0;
      if (!node) {
        var line = lineView.rest ? lst(lineView.rest) : lineView.line;
        return badPos(Pos(lineNo(line), line.text.length), bad);
      }
    }

    var textNode = node.nodeType == 3 ? node : null, topNode = node;
    if (!textNode && node.childNodes.length == 1 && node.firstChild.nodeType == 3) {
      textNode = node.firstChild;
      if (offset) offset = textNode.nodeValue.length;
    }
    while (topNode.parentNode != wrapper) topNode = topNode.parentNode;
    var measure = lineView.measure, maps = measure.maps;

    function find(textNode, topNode, offset) {
      for (var i = -1; i < (maps ? maps.length : 0); i++) {
        var map = i < 0 ? measure.map : maps[i];
        for (var j = 0; j < map.length; j += 3) {
          var curNode = map[j + 2];
          if (curNode == textNode || curNode == topNode) {
            var line = lineNo(i < 0 ? lineView.line : lineView.rest[i]);
            var ch = map[j] + offset;
            if (offset < 0 || curNode != textNode) ch = map[j + (offset ? 1 : 0)];
            return Pos(line, ch);
          }
        }
      }
    }
    var found = find(textNode, topNode, offset);
    if (found) return badPos(found, bad);

    // FIXME this is all really shaky. might handle the few cases it needs to handle, but likely to cause problems
    for (var after = topNode.nextSibling, dist = textNode ? textNode.nodeValue.length - offset : 0; after; after = after.nextSibling) {
      found = find(after, after.firstChild, 0);
      if (found)
        return badPos(Pos(found.line, found.ch - dist), bad);
      else
        dist += after.textContent.length;
    }
    for (var before = topNode.previousSibling, dist = offset; before; before = before.previousSibling) {
      found = find(before, before.firstChild, -1);
      if (found)
        return badPos(Pos(found.line, found.ch + dist), bad);
      else
        dist += after.textContent.length;
    }
  }

  function domTextBetween(cm, from, to, fromLine, toLine) {
    var text = "", closing = false, lineSep = cm.doc.lineSeparator();
    function recognizeMarker(id) { return function(marker) { return marker.id == id; }; }
    function walk(node) {
      if (node.nodeType == 1) {
        var cmText = node.getAttribute("cm-text");
        if (cmText != null) {
          if (cmText == "") cmText = node.textContent.replace(/\u200b/g, "");
          text += cmText;
          return;
        }
        var markerID = node.getAttribute("cm-marker"), range;
        if (markerID) {
          var found = cm.findMarks(Pos(fromLine, 0), Pos(toLine + 1, 0), recognizeMarker(+markerID));
          if (found.length && (range = found[0].find()))
            text += getBetween(cm.doc, range.from, range.to).join(lineSep);
          return;
        }
        if (node.getAttribute("contenteditable") == "false") return;
        for (var i = 0; i < node.childNodes.length; i++)
          walk(node.childNodes[i]);
        if (/^(pre|div|p)$/i.test(node.nodeName))
          closing = true;
      } else if (node.nodeType == 3) {
        var val = node.nodeValue;
        if (!val) return;
        if (closing) {
          text += lineSep;
          closing = false;
        }
        text += val;
      }
    }
    for (;;) {
      walk(from);
      if (from == to) break;
      from = from.nextSibling;
    }
    return text;
  }

  CodeMirror.inputStyles = {"textarea": TextareaInput, "contenteditable": ContentEditableInput};

  // SELECTION / CURSOR

  // Selection objects are immutable. A new one is created every time
  // the selection changes. A selection is one or more non-overlapping
  // (and non-touching) ranges, sorted, and an integer that indicates
  // which one is the primary selection (the one that's scrolled into
  // view, that getCursor returns, etc).
  function Selection(ranges, primIndex) {
    this.ranges = ranges;
    this.primIndex = primIndex;
  }

  Selection.prototype = {
    primary: function() { return this.ranges[this.primIndex]; },
    equals: function(other) {
      if (other == this) return true;
      if (other.primIndex != this.primIndex || other.ranges.length != this.ranges.length) return false;
      for (var i = 0; i < this.ranges.length; i++) {
        var here = this.ranges[i], there = other.ranges[i];
        if (cmp(here.anchor, there.anchor) != 0 || cmp(here.head, there.head) != 0) return false;
      }
      return true;
    },
    deepCopy: function() {
      for (var out = [], i = 0; i < this.ranges.length; i++)
        out[i] = new Range(copyPos(this.ranges[i].anchor), copyPos(this.ranges[i].head));
      return new Selection(out, this.primIndex);
    },
    somethingSelected: function() {
      for (var i = 0; i < this.ranges.length; i++)
        if (!this.ranges[i].empty()) return true;
      return false;
    },
    contains: function(pos, end) {
      if (!end) end = pos;
      for (var i = 0; i < this.ranges.length; i++) {
        var range = this.ranges[i];
        if (cmp(end, range.from()) >= 0 && cmp(pos, range.to()) <= 0)
          return i;
      }
      return -1;
    }
  };

  function Range(anchor, head) {
    this.anchor = anchor; this.head = head;
  }

  Range.prototype = {
    from: function() { return minPos(this.anchor, this.head); },
    to: function() { return maxPos(this.anchor, this.head); },
    empty: function() {
      return this.head.line == this.anchor.line && this.head.ch == this.anchor.ch;
    }
  };

  // Take an unsorted, potentially overlapping set of ranges, and
  // build a selection out of it. 'Consumes' ranges array (modifying
  // it).
  function normalizeSelection(ranges, primIndex) {
    var prim = ranges[primIndex];
    ranges.sort(function(a, b) { return cmp(a.from(), b.from()); });
    primIndex = indexOf(ranges, prim);
    for (var i = 1; i < ranges.length; i++) {
      var cur = ranges[i], prev = ranges[i - 1];
      if (cmp(prev.to(), cur.from()) >= 0) {
        var from = minPos(prev.from(), cur.from()), to = maxPos(prev.to(), cur.to());
        var inv = prev.empty() ? cur.from() == cur.head : prev.from() == prev.head;
        if (i <= primIndex) --primIndex;
        ranges.splice(--i, 2, new Range(inv ? to : from, inv ? from : to));
      }
    }
    return new Selection(ranges, primIndex);
  }

  function simpleSelection(anchor, head) {
    return new Selection([new Range(anchor, head || anchor)], 0);
  }

  // Most of the external API clips given positions to make sure they
  // actually exist within the document.
  function clipLine(doc, n) {return Math.max(doc.first, Math.min(n, doc.first + doc.size - 1));}
  function clipPos(doc, pos) {
    if (pos.line < doc.first) return Pos(doc.first, 0);
    var last = doc.first + doc.size - 1;
    if (pos.line > last) return Pos(last, getLine(doc, last).text.length);
    return clipToLen(pos, getLine(doc, pos.line).text.length);
  }
  function clipToLen(pos, linelen) {
    var ch = pos.ch;
    if (ch == null || ch > linelen) return Pos(pos.line, linelen);
    else if (ch < 0) return Pos(pos.line, 0);
    else return pos;
  }
  function isLine(doc, l) {return l >= doc.first && l < doc.first + doc.size;}
  function clipPosArray(doc, array) {
    for (var out = [], i = 0; i < array.length; i++) out[i] = clipPos(doc, array[i]);
    return out;
  }

  // SELECTION UPDATES

  // The 'scroll' parameter given to many of these indicated whether
  // the new cursor position should be scrolled into view after
  // modifying the selection.

  // If shift is held or the extend flag is set, extends a range to
  // include a given position (and optionally a second position).
  // Otherwise, simply returns the range between the given positions.
  // Used for cursor motion and such.
  function extendRange(doc, range, head, other) {
    if (doc.cm && doc.cm.display.shift || doc.extend) {
      var anchor = range.anchor;
      if (other) {
        var posBefore = cmp(head, anchor) < 0;
        if (posBefore != (cmp(other, anchor) < 0)) {
          anchor = head;
          head = other;
        } else if (posBefore != (cmp(head, other) < 0)) {
          head = other;
        }
      }
      return new Range(anchor, head);
    } else {
      return new Range(other || head, head);
    }
  }

  // Extend the primary selection range, discard the rest.
  function extendSelection(doc, head, other, options) {
    setSelection(doc, new Selection([extendRange(doc, doc.sel.primary(), head, other)], 0), options);
  }

  // Extend all selections (pos is an array of selections with length
  // equal the number of selections)
  function extendSelections(doc, heads, options) {
    for (var out = [], i = 0; i < doc.sel.ranges.length; i++)
      out[i] = extendRange(doc, doc.sel.ranges[i], heads[i], null);
    var newSel = normalizeSelection(out, doc.sel.primIndex);
    setSelection(doc, newSel, options);
  }

  // Updates a single range in the selection.
  function replaceOneSelection(doc, i, range, options) {
    var ranges = doc.sel.ranges.slice(0);
    ranges[i] = range;
    setSelection(doc, normalizeSelection(ranges, doc.sel.primIndex), options);
  }

  // Reset the selection to a single range.
  function setSimpleSelection(doc, anchor, head, options) {
    setSelection(doc, simpleSelection(anchor, head), options);
  }

  // Give beforeSelectionChange handlers a change to influence a
  // selection update.
  function filterSelectionChange(doc, sel, options) {
    var obj = {
      ranges: sel.ranges,
      update: function(ranges) {
        this.ranges = [];
        for (var i = 0; i < ranges.length; i++)
          this.ranges[i] = new Range(clipPos(doc, ranges[i].anchor),
                                     clipPos(doc, ranges[i].head));
      },
      origin: options && options.origin
    };
    signal(doc, "beforeSelectionChange", doc, obj);
    if (doc.cm) signal(doc.cm, "beforeSelectionChange", doc.cm, obj);
    if (obj.ranges != sel.ranges) return normalizeSelection(obj.ranges, obj.ranges.length - 1);
    else return sel;
  }

  function setSelectionReplaceHistory(doc, sel, options) {
    var done = doc.history.done, last = lst(done);
    if (last && last.ranges) {
      done[done.length - 1] = sel;
      setSelectionNoUndo(doc, sel, options);
    } else {
      setSelection(doc, sel, options);
    }
  }

  // Set a new selection.
  function setSelection(doc, sel, options) {
    setSelectionNoUndo(doc, sel, options);
    addSelectionToHistory(doc, doc.sel, doc.cm ? doc.cm.curOp.id : NaN, options);
  }

  function setSelectionNoUndo(doc, sel, options) {
    if (hasHandler(doc, "beforeSelectionChange") || doc.cm && hasHandler(doc.cm, "beforeSelectionChange"))
      sel = filterSelectionChange(doc, sel, options);

    var bias = options && options.bias ||
      (cmp(sel.primary().head, doc.sel.primary().head) < 0 ? -1 : 1);
    setSelectionInner(doc, skipAtomicInSelection(doc, sel, bias, true));

    if (!(options && options.scroll === false) && doc.cm)
      ensureCursorVisible(doc.cm);
  }

  function setSelectionInner(doc, sel) {
    if (sel.equals(doc.sel)) return;

    doc.sel = sel;

    if (doc.cm) {
      doc.cm.curOp.updateInput = doc.cm.curOp.selectionChanged = true;
      signalCursorActivity(doc.cm);
    }
    signalLater(doc, "cursorActivity", doc);
  }

  // Verify that the selection does not partially select any atomic
  // marked ranges.
  function reCheckSelection(doc) {
    setSelectionInner(doc, skipAtomicInSelection(doc, doc.sel, null, false), sel_dontScroll);
  }

  // Return a selection that does not partially select any atomic
  // ranges.
  function skipAtomicInSelection(doc, sel, bias, mayClear) {
    var out;
    for (var i = 0; i < sel.ranges.length; i++) {
      var range = sel.ranges[i];
      var old = sel.ranges.length == doc.sel.ranges.length && doc.sel.ranges[i];
      var newAnchor = skipAtomic(doc, range.anchor, old && old.anchor, bias, mayClear);
      var newHead = skipAtomic(doc, range.head, old && old.head, bias, mayClear);
      if (out || newAnchor != range.anchor || newHead != range.head) {
        if (!out) out = sel.ranges.slice(0, i);
        out[i] = new Range(newAnchor, newHead);
      }
    }
    return out ? normalizeSelection(out, sel.primIndex) : sel;
  }

  function skipAtomicInner(doc, pos, oldPos, dir, mayClear) {
    var line = getLine(doc, pos.line);
    if (line.markedSpans) for (var i = 0; i < line.markedSpans.length; ++i) {
      var sp = line.markedSpans[i], m = sp.marker;
      if ((sp.from == null || (m.inclusiveLeft ? sp.from <= pos.ch : sp.from < pos.ch)) &&
          (sp.to == null || (m.inclusiveRight ? sp.to >= pos.ch : sp.to > pos.ch))) {
        if (mayClear) {
          signal(m, "beforeCursorEnter");
          if (m.explicitlyCleared) {
            if (!line.markedSpans) break;
            else {--i; continue;}
          }
        }
        if (!m.atomic) continue;

        if (oldPos) {
          var near = m.find(dir < 0 ? 1 : -1), diff;
          if (dir < 0 ? m.inclusiveRight : m.inclusiveLeft)
            near = movePos(doc, near, -dir, near && near.line == pos.line ? line : null);
          if (near && near.line == pos.line && (diff = cmp(near, oldPos)) && (dir < 0 ? diff < 0 : diff > 0))
            return skipAtomicInner(doc, near, pos, dir, mayClear);
        }

        var far = m.find(dir < 0 ? -1 : 1);
        if (dir < 0 ? m.inclusiveLeft : m.inclusiveRight)
          far = movePos(doc, far, dir, far.line == pos.line ? line : null);
        return far ? skipAtomicInner(doc, far, pos, dir, mayClear) : null;
      }
    }
    return pos;
  }

  // Ensure a given position is not inside an atomic range.
  function skipAtomic(doc, pos, oldPos, bias, mayClear) {
    var dir = bias || 1;
    var found = skipAtomicInner(doc, pos, oldPos, dir, mayClear) ||
        (!mayClear && skipAtomicInner(doc, pos, oldPos, dir, true)) ||
        skipAtomicInner(doc, pos, oldPos, -dir, mayClear) ||
        (!mayClear && skipAtomicInner(doc, pos, oldPos, -dir, true));
    if (!found) {
      doc.cantEdit = true;
      return Pos(doc.first, 0);
    }
    return found;
  }

  function movePos(doc, pos, dir, line) {
    if (dir < 0 && pos.ch == 0) {
      if (pos.line > doc.first) return clipPos(doc, Pos(pos.line - 1));
      else return null;
    } else if (dir > 0 && pos.ch == (line || getLine(doc, pos.line)).text.length) {
      if (pos.line < doc.first + doc.size - 1) return Pos(pos.line + 1, 0);
      else return null;
    } else {
      return new Pos(pos.line, pos.ch + dir);
    }
  }

  // SELECTION DRAWING

  function updateSelection(cm) {
    cm.display.input.showSelection(cm.display.input.prepareSelection());
  }

  function prepareSelection(cm, primary) {
    var doc = cm.doc, result = {};
    var curFragment = result.cursors = document.createDocumentFragment();
    var selFragment = result.selection = document.createDocumentFragment();

    for (var i = 0; i < doc.sel.ranges.length; i++) {
      if (primary === false && i == doc.sel.primIndex) continue;
      var range = doc.sel.ranges[i];
      if (range.from().line >= cm.display.viewTo || range.to().line < cm.display.viewFrom) continue;
      var collapsed = range.empty();
      if (collapsed || cm.options.showCursorWhenSelecting)
        drawSelectionCursor(cm, range.head, curFragment);
      if (!collapsed)
        drawSelectionRange(cm, range, selFragment);
    }
    return result;
  }

  // Draws a cursor for the given range
  function drawSelectionCursor(cm, head, output) {
    var pos = cursorCoords(cm, head, "div", null, null, !cm.options.singleCursorHeightPerLine);

    var cursor = output.appendChild(elt("div", "\u00a0", "CodeMirror-cursor"));
    cursor.style.left = pos.left + "px";
    cursor.style.top = pos.top + "px";
    cursor.style.height = Math.max(0, pos.bottom - pos.top) * cm.options.cursorHeight + "px";

    if (pos.other) {
      // Secondary cursor, shown when on a 'jump' in bi-directional text
      var otherCursor = output.appendChild(elt("div", "\u00a0", "CodeMirror-cursor CodeMirror-secondarycursor"));
      otherCursor.style.display = "";
      otherCursor.style.left = pos.other.left + "px";
      otherCursor.style.top = pos.other.top + "px";
      otherCursor.style.height = (pos.other.bottom - pos.other.top) * .85 + "px";
    }
  }

  // Draws the given range as a highlighted selection
  function drawSelectionRange(cm, range, output) {
    var display = cm.display, doc = cm.doc;
    var fragment = document.createDocumentFragment();
    var padding = paddingH(cm.display), leftSide = padding.left;
    var rightSide = Math.max(display.sizerWidth, displayWidth(cm) - display.sizer.offsetLeft) - padding.right;

    function add(left, top, width, bottom) {
      if (top < 0) top = 0;
      top = Math.round(top);
      bottom = Math.round(bottom);
      fragment.appendChild(elt("div", null, "CodeMirror-selected", "position: absolute; left: " + left +
                               "px; top: " + top + "px; width: " + (width == null ? rightSide - left : width) +
                               "px; height: " + (bottom - top) + "px"));
    }

    function drawForLine(line, fromArg, toArg) {
      var lineObj = getLine(doc, line);
      var lineLen = lineObj.text.length;
      var start, end;
      function coords(ch, bias) {
        return charCoords(cm, Pos(line, ch), "div", lineObj, bias);
      }

      iterateBidiSections(getOrder(lineObj), fromArg || 0, toArg == null ? lineLen : toArg, function(from, to, dir) {
        var leftPos = coords(from, "left"), rightPos, left, right;
        if (from == to) {
          rightPos = leftPos;
          left = right = leftPos.left;
        } else {
          rightPos = coords(to - 1, "right");
          if (dir == "rtl") { var tmp = leftPos; leftPos = rightPos; rightPos = tmp; }
          left = leftPos.left;
          right = rightPos.right;
        }
        if (fromArg == null && from == 0) left = leftSide;
        if (rightPos.top - leftPos.top > 3) { // Different lines, draw top part
          add(left, leftPos.top, null, leftPos.bottom);
          left = leftSide;
          if (leftPos.bottom < rightPos.top) add(left, leftPos.bottom, null, rightPos.top);
        }
        if (toArg == null && to == lineLen) right = rightSide;
        if (!start || leftPos.top < start.top || leftPos.top == start.top && leftPos.left < start.left)
          start = leftPos;
        if (!end || rightPos.bottom > end.bottom || rightPos.bottom == end.bottom && rightPos.right > end.right)
          end = rightPos;
        if (left < leftSide + 1) left = leftSide;
        add(left, rightPos.top, right - left, rightPos.bottom);
      });
      return {start: start, end: end};
    }

    var sFrom = range.from(), sTo = range.to();
    if (sFrom.line == sTo.line) {
      drawForLine(sFrom.line, sFrom.ch, sTo.ch);
    } else {
      var fromLine = getLine(doc, sFrom.line), toLine = getLine(doc, sTo.line);
      var singleVLine = visualLine(fromLine) == visualLine(toLine);
      var leftEnd = drawForLine(sFrom.line, sFrom.ch, singleVLine ? fromLine.text.length + 1 : null).end;
      var rightStart = drawForLine(sTo.line, singleVLine ? 0 : null, sTo.ch).start;
      if (singleVLine) {
        if (leftEnd.top < rightStart.top - 2) {
          add(leftEnd.right, leftEnd.top, null, leftEnd.bottom);
          add(leftSide, rightStart.top, rightStart.left, rightStart.bottom);
        } else {
          add(leftEnd.right, leftEnd.top, rightStart.left - leftEnd.right, leftEnd.bottom);
        }
      }
      if (leftEnd.bottom < rightStart.top)
        add(leftSide, leftEnd.bottom, null, rightStart.top);
    }

    output.appendChild(fragment);
  }

  // Cursor-blinking
  function restartBlink(cm) {
    if (!cm.state.focused) return;
    var display = cm.display;
    clearInterval(display.blinker);
    var on = true;
    display.cursorDiv.style.visibility = "";
    if (cm.options.cursorBlinkRate > 0)
      display.blinker = setInterval(function() {
        display.cursorDiv.style.visibility = (on = !on) ? "" : "hidden";
      }, cm.options.cursorBlinkRate);
    else if (cm.options.cursorBlinkRate < 0)
      display.cursorDiv.style.visibility = "hidden";
  }

  // HIGHLIGHT WORKER

  function startWorker(cm, time) {
    if (cm.doc.mode.startState && cm.doc.frontier < cm.display.viewTo)
      cm.state.highlight.set(time, bind(highlightWorker, cm));
  }

  function highlightWorker(cm) {
    var doc = cm.doc;
    if (doc.frontier < doc.first) doc.frontier = doc.first;
    if (doc.frontier >= cm.display.viewTo) return;
    var end = +new Date + cm.options.workTime;
    var state = copyState(doc.mode, getStateBefore(cm, doc.frontier));
    var changedLines = [];

    doc.iter(doc.frontier, Math.min(doc.first + doc.size, cm.display.viewTo + 500), function(line) {
      if (doc.frontier >= cm.display.viewFrom) { // Visible
        var oldStyles = line.styles, tooLong = line.text.length > cm.options.maxHighlightLength;
        var highlighted = highlightLine(cm, line, tooLong ? copyState(doc.mode, state) : state, true);
        line.styles = highlighted.styles;
        var oldCls = line.styleClasses, newCls = highlighted.classes;
        if (newCls) line.styleClasses = newCls;
        else if (oldCls) line.styleClasses = null;
        var ischange = !oldStyles || oldStyles.length != line.styles.length ||
          oldCls != newCls && (!oldCls || !newCls || oldCls.bgClass != newCls.bgClass || oldCls.textClass != newCls.textClass);
        for (var i = 0; !ischange && i < oldStyles.length; ++i) ischange = oldStyles[i] != line.styles[i];
        if (ischange) changedLines.push(doc.frontier);
        line.stateAfter = tooLong ? state : copyState(doc.mode, state);
      } else {
        if (line.text.length <= cm.options.maxHighlightLength)
          processLine(cm, line.text, state);
        line.stateAfter = doc.frontier % 5 == 0 ? copyState(doc.mode, state) : null;
      }
      ++doc.frontier;
      if (+new Date > end) {
        startWorker(cm, cm.options.workDelay);
        return true;
      }
    });
    if (changedLines.length) runInOp(cm, function() {
      for (var i = 0; i < changedLines.length; i++)
        regLineChange(cm, changedLines[i], "text");
    });
  }

  // Finds the line to start with when starting a parse. Tries to
  // find a line with a stateAfter, so that it can start with a
  // valid state. If that fails, it returns the line with the
  // smallest indentation, which tends to need the least context to
  // parse correctly.
  function findStartLine(cm, n, precise) {
    var minindent, minline, doc = cm.doc;
    var lim = precise ? -1 : n - (cm.doc.mode.innerMode ? 1000 : 100);
    for (var search = n; search > lim; --search) {
      if (search <= doc.first) return doc.first;
      var line = getLine(doc, search - 1);
      if (line.stateAfter && (!precise || search <= doc.frontier)) return search;
      var indented = countColumn(line.text, null, cm.options.tabSize);
      if (minline == null || minindent > indented) {
        minline = search - 1;
        minindent = indented;
      }
    }
    return minline;
  }

  function getStateBefore(cm, n, precise) {
    var doc = cm.doc, display = cm.display;
    if (!doc.mode.startState) return true;
    var pos = findStartLine(cm, n, precise), state = pos > doc.first && getLine(doc, pos-1).stateAfter;
    if (!state) state = startState(doc.mode);
    else state = copyState(doc.mode, state);
    doc.iter(pos, n, function(line) {
      processLine(cm, line.text, state);
      var save = pos == n - 1 || pos % 5 == 0 || pos >= display.viewFrom && pos < display.viewTo;
      line.stateAfter = save ? copyState(doc.mode, state) : null;
      ++pos;
    });
    if (precise) doc.frontier = pos;
    return state;
  }

  // POSITION MEASUREMENT

  function paddingTop(display) {return display.lineSpace.offsetTop;}
  function paddingVert(display) {return display.mover.offsetHeight - display.lineSpace.offsetHeight;}
  function paddingH(display) {
    if (display.cachedPaddingH) return display.cachedPaddingH;
    var e = removeChildrenAndAdd(display.measure, elt("pre", "x"));
    var style = window.getComputedStyle ? window.getComputedStyle(e) : e.currentStyle;
    var data = {left: parseInt(style.paddingLeft), right: parseInt(style.paddingRight)};
    if (!isNaN(data.left) && !isNaN(data.right)) display.cachedPaddingH = data;
    return data;
  }

  function scrollGap(cm) { return scrollerGap - cm.display.nativeBarWidth; }
  function displayWidth(cm) {
    return cm.display.scroller.clientWidth - scrollGap(cm) - cm.display.barWidth;
  }
  function displayHeight(cm) {
    return cm.display.scroller.clientHeight - scrollGap(cm) - cm.display.barHeight;
  }

  // Ensure the lineView.wrapping.heights array is populated. This is
  // an array of bottom offsets for the lines that make up a drawn
  // line. When lineWrapping is on, there might be more than one
  // height.
  function ensureLineHeights(cm, lineView, rect) {
    var wrapping = cm.options.lineWrapping;
    var curWidth = wrapping && displayWidth(cm);
    if (!lineView.measure.heights || wrapping && lineView.measure.width != curWidth) {
      var heights = lineView.measure.heights = [];
      if (wrapping) {
        lineView.measure.width = curWidth;
        var rects = lineView.text.firstChild.getClientRects();
        for (var i = 0; i < rects.length - 1; i++) {
          var cur = rects[i], next = rects[i + 1];
          if (Math.abs(cur.bottom - next.bottom) > 2)
            heights.push((cur.bottom + next.top) / 2 - rect.top);
        }
      }
      heights.push(rect.bottom - rect.top);
    }
  }

  // Find a line map (mapping character offsets to text nodes) and a
  // measurement cache for the given line number. (A line view might
  // contain multiple lines when collapsed ranges are present.)
  function mapFromLineView(lineView, line, lineN) {
    if (lineView.line == line)
      return {map: lineView.measure.map, cache: lineView.measure.cache};
    for (var i = 0; i < lineView.rest.length; i++)
      if (lineView.rest[i] == line)
        return {map: lineView.measure.maps[i], cache: lineView.measure.caches[i]};
    for (var i = 0; i < lineView.rest.length; i++)
      if (lineNo(lineView.rest[i]) > lineN)
        return {map: lineView.measure.maps[i], cache: lineView.measure.caches[i], before: true};
  }

  // Render a line into the hidden node display.externalMeasured. Used
  // when measurement is needed for a line that's not in the viewport.
  function updateExternalMeasurement(cm, line) {
    line = visualLine(line);
    var lineN = lineNo(line);
    var view = cm.display.externalMeasured = new LineView(cm.doc, line, lineN);
    view.lineN = lineN;
    var built = view.built = buildLineContent(cm, view);
    view.text = built.pre;
    removeChildrenAndAdd(cm.display.lineMeasure, built.pre);
    return view;
  }

  // Get a {top, bottom, left, right} box (in line-local coordinates)
  // for a given character.
  function measureChar(cm, line, ch, bias) {
    return measureCharPrepared(cm, prepareMeasureForLine(cm, line), ch, bias);
  }

  // Find a line view that corresponds to the given line number.
  function findViewForLine(cm, lineN) {
    if (lineN >= cm.display.viewFrom && lineN < cm.display.viewTo)
      return cm.display.view[findViewIndex(cm, lineN)];
    var ext = cm.display.externalMeasured;
    if (ext && lineN >= ext.lineN && lineN < ext.lineN + ext.size)
      return ext;
  }

  // Measurement can be split in two steps, the set-up work that
  // applies to the whole line, and the measurement of the actual
  // character. Functions like coordsChar, that need to do a lot of
  // measurements in a row, can thus ensure that the set-up work is
  // only done once.
  function prepareMeasureForLine(cm, line) {
    var lineN = lineNo(line);
    var view = findViewForLine(cm, lineN);
    if (view && !view.text) {
      view = null;
    } else if (view && view.changes) {
      updateLineForChanges(cm, view, lineN, getDimensions(cm));
      cm.curOp.forceUpdate = true;
    }
    if (!view)
      view = updateExternalMeasurement(cm, line);

    var info = mapFromLineView(view, line, lineN);
    return {
      line: line, view: view, rect: null,
      map: info.map, cache: info.cache, before: info.before,
      hasHeights: false
    };
  }

  // Given a prepared measurement object, measures the position of an
  // actual character (or fetches it from the cache).
  function measureCharPrepared(cm, prepared, ch, bias, varHeight) {
    if (prepared.before) ch = -1;
    var key = ch + (bias || ""), found;
    if (prepared.cache.hasOwnProperty(key)) {
      found = prepared.cache[key];
    } else {
      if (!prepared.rect)
        prepared.rect = prepared.view.text.getBoundingClientRect();
      if (!prepared.hasHeights) {
        ensureLineHeights(cm, prepared.view, prepared.rect);
        prepared.hasHeights = true;
      }
      found = measureCharInner(cm, prepared, ch, bias);
      if (!found.bogus) prepared.cache[key] = found;
    }
    return {left: found.left, right: found.right,
            top: varHeight ? found.rtop : found.top,
            bottom: varHeight ? found.rbottom : found.bottom};
  }

  var nullRect = {left: 0, right: 0, top: 0, bottom: 0};

  function nodeAndOffsetInLineMap(map, ch, bias) {
    var node, start, end, collapse;
    // First, search the line map for the text node corresponding to,
    // or closest to, the target character.
    for (var i = 0; i < map.length; i += 3) {
      var mStart = map[i], mEnd = map[i + 1];
      if (ch < mStart) {
        start = 0; end = 1;
        collapse = "left";
      } else if (ch < mEnd) {
        start = ch - mStart;
        end = start + 1;
      } else if (i == map.length - 3 || ch == mEnd && map[i + 3] > ch) {
        end = mEnd - mStart;
        start = end - 1;
        if (ch >= mEnd) collapse = "right";
      }
      if (start != null) {
        node = map[i + 2];
        if (mStart == mEnd && bias == (node.insertLeft ? "left" : "right"))
          collapse = bias;
        if (bias == "left" && start == 0)
          while (i && map[i - 2] == map[i - 3] && map[i - 1].insertLeft) {
            node = map[(i -= 3) + 2];
            collapse = "left";
          }
        if (bias == "right" && start == mEnd - mStart)
          while (i < map.length - 3 && map[i + 3] == map[i + 4] && !map[i + 5].insertLeft) {
            node = map[(i += 3) + 2];
            collapse = "right";
          }
        break;
      }
    }
    return {node: node, start: start, end: end, collapse: collapse, coverStart: mStart, coverEnd: mEnd};
  }

  function measureCharInner(cm, prepared, ch, bias) {
    var place = nodeAndOffsetInLineMap(prepared.map, ch, bias);
    var node = place.node, start = place.start, end = place.end, collapse = place.collapse;

    var rect;
    if (node.nodeType == 3) { // If it is a text node, use a range to retrieve the coordinates.
      for (var i = 0; i < 4; i++) { // Retry a maximum of 4 times when nonsense rectangles are returned
        while (start && isExtendingChar(prepared.line.text.charAt(place.coverStart + start))) --start;
        while (place.coverStart + end < place.coverEnd && isExtendingChar(prepared.line.text.charAt(place.coverStart + end))) ++end;
        if (ie && ie_version < 9 && start == 0 && end == place.coverEnd - place.coverStart) {
          rect = node.parentNode.getBoundingClientRect();
        } else if (ie && cm.options.lineWrapping) {
          var rects = range(node, start, end).getClientRects();
          if (rects.length)
            rect = rects[bias == "right" ? rects.length - 1 : 0];
          else
            rect = nullRect;
        } else {
          rect = range(node, start, end).getBoundingClientRect() || nullRect;
        }
        if (rect.left || rect.right || start == 0) break;
        end = start;
        start = start - 1;
        collapse = "right";
      }
      if (ie && ie_version < 11) rect = maybeUpdateRectForZooming(cm.display.measure, rect);
    } else { // If it is a widget, simply get the box for the whole widget.
      if (start > 0) collapse = bias = "right";
      var rects;
      if (cm.options.lineWrapping && (rects = node.getClientRects()).length > 1)
        rect = rects[bias == "right" ? rects.length - 1 : 0];
      else
        rect = node.getBoundingClientRect();
    }
    if (ie && ie_version < 9 && !start && (!rect || !rect.left && !rect.right)) {
      var rSpan = node.parentNode.getClientRects()[0];
      if (rSpan)
        rect = {left: rSpan.left, right: rSpan.left + charWidth(cm.display), top: rSpan.top, bottom: rSpan.bottom};
      else
        rect = nullRect;
    }

    var rtop = rect.top - prepared.rect.top, rbot = rect.bottom - prepared.rect.top;
    var mid = (rtop + rbot) / 2;
    var heights = prepared.view.measure.heights;
    for (var i = 0; i < heights.length - 1; i++)
      if (mid < heights[i]) break;
    var top = i ? heights[i - 1] : 0, bot = heights[i];
    var result = {left: (collapse == "right" ? rect.right : rect.left) - prepared.rect.left,
                  right: (collapse == "left" ? rect.left : rect.right) - prepared.rect.left,
                  top: top, bottom: bot};
    if (!rect.left && !rect.right) result.bogus = true;
    if (!cm.options.singleCursorHeightPerLine) { result.rtop = rtop; result.rbottom = rbot; }

    return result;
  }

  // Work around problem with bounding client rects on ranges being
  // returned incorrectly when zoomed on IE10 and below.
  function maybeUpdateRectForZooming(measure, rect) {
    if (!window.screen || screen.logicalXDPI == null ||
        screen.logicalXDPI == screen.deviceXDPI || !hasBadZoomedRects(measure))
      return rect;
    var scaleX = screen.logicalXDPI / screen.deviceXDPI;
    var scaleY = screen.logicalYDPI / screen.deviceYDPI;
    return {left: rect.left * scaleX, right: rect.right * scaleX,
            top: rect.top * scaleY, bottom: rect.bottom * scaleY};
  }

  function clearLineMeasurementCacheFor(lineView) {
    if (lineView.measure) {
      lineView.measure.cache = {};
      lineView.measure.heights = null;
      if (lineView.rest) for (var i = 0; i < lineView.rest.length; i++)
        lineView.measure.caches[i] = {};
    }
  }

  function clearLineMeasurementCache(cm) {
    cm.display.externalMeasure = null;
    removeChildren(cm.display.lineMeasure);
    for (var i = 0; i < cm.display.view.length; i++)
      clearLineMeasurementCacheFor(cm.display.view[i]);
  }

  function clearCaches(cm) {
    clearLineMeasurementCache(cm);
    cm.display.cachedCharWidth = cm.display.cachedTextHeight = cm.display.cachedPaddingH = null;
    if (!cm.options.lineWrapping) cm.display.maxLineChanged = true;
    cm.display.lineNumChars = null;
  }

  function pageScrollX() { return window.pageXOffset || (document.documentElement || document.body).scrollLeft; }
  function pageScrollY() { return window.pageYOffset || (document.documentElement || document.body).scrollTop; }

  // Converts a {top, bottom, left, right} box from line-local
  // coordinates into another coordinate system. Context may be one of
  // "line", "div" (display.lineDiv), "local"/null (editor), "window",
  // or "page".
  function intoCoordSystem(cm, lineObj, rect, context) {
    if (lineObj.widgets) for (var i = 0; i < lineObj.widgets.length; ++i) if (lineObj.widgets[i].above) {
      var size = widgetHeight(lineObj.widgets[i]);
      rect.top += size; rect.bottom += size;
    }
    if (context == "line") return rect;
    if (!context) context = "local";
    var yOff = heightAtLine(lineObj);
    if (context == "local") yOff += paddingTop(cm.display);
    else yOff -= cm.display.viewOffset;
    if (context == "page" || context == "window") {
      var lOff = cm.display.lineSpace.getBoundingClientRect();
      yOff += lOff.top + (context == "window" ? 0 : pageScrollY());
      var xOff = lOff.left + (context == "window" ? 0 : pageScrollX());
      rect.left += xOff; rect.right += xOff;
    }
    rect.top += yOff; rect.bottom += yOff;
    return rect;
  }

  // Coverts a box from "div" coords to another coordinate system.
  // Context may be "window", "page", "div", or "local"/null.
  function fromCoordSystem(cm, coords, context) {
    if (context == "div") return coords;
    var left = coords.left, top = coords.top;
    // First move into "page" coordinate system
    if (context == "page") {
      left -= pageScrollX();
      top -= pageScrollY();
    } else if (context == "local" || !context) {
      var localBox = cm.display.sizer.getBoundingClientRect();
      left += localBox.left;
      top += localBox.top;
    }

    var lineSpaceBox = cm.display.lineSpace.getBoundingClientRect();
    return {left: left - lineSpaceBox.left, top: top - lineSpaceBox.top};
  }

  function charCoords(cm, pos, context, lineObj, bias) {
    if (!lineObj) lineObj = getLine(cm.doc, pos.line);
    return intoCoordSystem(cm, lineObj, measureChar(cm, lineObj, pos.ch, bias), context);
  }

  // Returns a box for a given cursor position, which may have an
  // 'other' property containing the position of the secondary cursor
  // on a bidi boundary.
  function cursorCoords(cm, pos, context, lineObj, preparedMeasure, varHeight) {
    lineObj = lineObj || getLine(cm.doc, pos.line);
    if (!preparedMeasure) preparedMeasure = prepareMeasureForLine(cm, lineObj);
    function get(ch, right) {
      var m = measureCharPrepared(cm, preparedMeasure, ch, right ? "right" : "left", varHeight);
      if (right) m.left = m.right; else m.right = m.left;
      return intoCoordSystem(cm, lineObj, m, context);
    }
    function getBidi(ch, partPos) {
      var part = order[partPos], right = part.level % 2;
      if (ch == bidiLeft(part) && partPos && part.level < order[partPos - 1].level) {
        part = order[--partPos];
        ch = bidiRight(part) - (part.level % 2 ? 0 : 1);
        right = true;
      } else if (ch == bidiRight(part) && partPos < order.length - 1 && part.level < order[partPos + 1].level) {
        part = order[++partPos];
        ch = bidiLeft(part) - part.level % 2;
        right = false;
      }
      if (right && ch == part.to && ch > part.from) return get(ch - 1);
      return get(ch, right);
    }
    var order = getOrder(lineObj), ch = pos.ch;
    if (!order) return get(ch);
    var partPos = getBidiPartAt(order, ch);
    var val = getBidi(ch, partPos);
    if (bidiOther != null) val.other = getBidi(ch, bidiOther);
    return val;
  }

  // Used to cheaply estimate the coordinates for a position. Used for
  // intermediate scroll updates.
  function estimateCoords(cm, pos) {
    var left = 0, pos = clipPos(cm.doc, pos);
    if (!cm.options.lineWrapping) left = charWidth(cm.display) * pos.ch;
    var lineObj = getLine(cm.doc, pos.line);
    var top = heightAtLine(lineObj) + paddingTop(cm.display);
    return {left: left, right: left, top: top, bottom: top + lineObj.height};
  }

  // Positions returned by coordsChar contain some extra information.
  // xRel is the relative x position of the input coordinates compared
  // to the found position (so xRel > 0 means the coordinates are to
  // the right of the character position, for example). When outside
  // is true, that means the coordinates lie outside the line's
  // vertical range.
  function PosWithInfo(line, ch, outside, xRel) {
    var pos = Pos(line, ch);
    pos.xRel = xRel;
    if (outside) pos.outside = true;
    return pos;
  }

  // Compute the character position closest to the given coordinates.
  // Input must be lineSpace-local ("div" coordinate system).
  function coordsChar(cm, x, y) {
    var doc = cm.doc;
    y += cm.display.viewOffset;
    if (y < 0) return PosWithInfo(doc.first, 0, true, -1);
    var lineN = lineAtHeight(doc, y), last = doc.first + doc.size - 1;
    if (lineN > last)
      return PosWithInfo(doc.first + doc.size - 1, getLine(doc, last).text.length, true, 1);
    if (x < 0) x = 0;

    var lineObj = getLine(doc, lineN);
    for (;;) {
      var found = coordsCharInner(cm, lineObj, lineN, x, y);
      var merged = collapsedSpanAtEnd(lineObj);
      var mergedPos = merged && merged.find(0, true);
      if (merged && (found.ch > mergedPos.from.ch || found.ch == mergedPos.from.ch && found.xRel > 0))
        lineN = lineNo(lineObj = mergedPos.to.line);
      else
        return found;
    }
  }

  function coordsCharInner(cm, lineObj, lineNo, x, y) {
    var innerOff = y - heightAtLine(lineObj);
    var wrongLine = false, adjust = 2 * cm.display.wrapper.clientWidth;
    var preparedMeasure = prepareMeasureForLine(cm, lineObj);

    function getX(ch) {
      var sp = cursorCoords(cm, Pos(lineNo, ch), "line", lineObj, preparedMeasure);
      wrongLine = true;
      if (innerOff > sp.bottom) return sp.left - adjust;
      else if (innerOff < sp.top) return sp.left + adjust;
      else wrongLine = false;
      return sp.left;
    }

    var bidi = getOrder(lineObj), dist = lineObj.text.length;
    var from = lineLeft(lineObj), to = lineRight(lineObj);
    var fromX = getX(from), fromOutside = wrongLine, toX = getX(to), toOutside = wrongLine;

    if (x > toX) return PosWithInfo(lineNo, to, toOutside, 1);
    // Do a binary search between these bounds.
    for (;;) {
      if (bidi ? to == from || to == moveVisually(lineObj, from, 1) : to - from <= 1) {
        var ch = x < fromX || x - fromX <= toX - x ? from : to;
        var outside = ch == from ? fromOutside : toOutside
        var xDiff = x - (ch == from ? fromX : toX);
        // This is a kludge to handle the case where the coordinates
        // are after a line-wrapped line. We should replace it with a
        // more general handling of cursor positions around line
        // breaks. (Issue #4078)
        if (toOutside && !bidi && !/\s/.test(lineObj.text.charAt(ch)) && xDiff > 0 &&
            ch < lineObj.text.length && preparedMeasure.view.measure.heights.length > 1) {
          var charSize = measureCharPrepared(cm, preparedMeasure, ch, "right");
          if (innerOff <= charSize.bottom && innerOff >= charSize.top && Math.abs(x - charSize.right) < xDiff) {
            outside = false
            ch++
            xDiff = x - charSize.right
          }
        }
        while (isExtendingChar(lineObj.text.charAt(ch))) ++ch;
        var pos = PosWithInfo(lineNo, ch, outside, xDiff < -1 ? -1 : xDiff > 1 ? 1 : 0);
        return pos;
      }
      var step = Math.ceil(dist / 2), middle = from + step;
      if (bidi) {
        middle = from;
        for (var i = 0; i < step; ++i) middle = moveVisually(lineObj, middle, 1);
      }
      var middleX = getX(middle);
      if (middleX > x) {to = middle; toX = middleX; if (toOutside = wrongLine) toX += 1000; dist = step;}
      else {from = middle; fromX = middleX; fromOutside = wrongLine; dist -= step;}
    }
  }

  var measureText;
  // Compute the default text height.
  function textHeight(display) {
    if (display.cachedTextHeight != null) return display.cachedTextHeight;
    if (measureText == null) {
      measureText = elt("pre");
      // Measure a bunch of lines, for browsers that compute
      // fractional heights.
      for (var i = 0; i < 49; ++i) {
        measureText.appendChild(document.createTextNode("x"));
        measureText.appendChild(elt("br"));
      }
      measureText.appendChild(document.createTextNode("x"));
    }
    removeChildrenAndAdd(display.measure, measureText);
    var height = measureText.offsetHeight / 50;
    if (height > 3) display.cachedTextHeight = height;
    removeChildren(display.measure);
    return height || 1;
  }

  // Compute the default character width.
  function charWidth(display) {
    if (display.cachedCharWidth != null) return display.cachedCharWidth;
    var anchor = elt("span", "xxxxxxxxxx");
    var pre = elt("pre", [anchor]);
    removeChildrenAndAdd(display.measure, pre);
    var rect = anchor.getBoundingClientRect(), width = (rect.right - rect.left) / 10;
    if (width > 2) display.cachedCharWidth = width;
    return width || 10;
  }

  // OPERATIONS

  // Operations are used to wrap a series of changes to the editor
  // state in such a way that each change won't have to update the
  // cursor and display (which would be awkward, slow, and
  // error-prone). Instead, display updates are batched and then all
  // combined and executed at once.

  var operationGroup = null;

  var nextOpId = 0;
  // Start a new operation.
  function startOperation(cm) {
    cm.curOp = {
      cm: cm,
      viewChanged: false,      // Flag that indicates that lines might need to be redrawn
      startHeight: cm.doc.height, // Used to detect need to update scrollbar
      forceUpdate: false,      // Used to force a redraw
      updateInput: null,       // Whether to reset the input textarea
      typing: false,           // Whether this reset should be careful to leave existing text (for compositing)
      changeObjs: null,        // Accumulated changes, for firing change events
      cursorActivityHandlers: null, // Set of handlers to fire cursorActivity on
      cursorActivityCalled: 0, // Tracks which cursorActivity handlers have been called already
      selectionChanged: false, // Whether the selection needs to be redrawn
      updateMaxLine: false,    // Set when the widest line needs to be determined anew
      scrollLeft: null, scrollTop: null, // Intermediate scroll position, not pushed to DOM yet
      scrollToPos: null,       // Used to scroll to a specific position
      focus: false,
      id: ++nextOpId           // Unique ID
    };
    if (operationGroup) {
      operationGroup.ops.push(cm.curOp);
    } else {
      cm.curOp.ownsGroup = operationGroup = {
        ops: [cm.curOp],
        delayedCallbacks: []
      };
    }
  }

  function fireCallbacksForOps(group) {
    // Calls delayed callbacks and cursorActivity handlers until no
    // new ones appear
    var callbacks = group.delayedCallbacks, i = 0;
    do {
      for (; i < callbacks.length; i++)
        callbacks[i].call(null);
      for (var j = 0; j < group.ops.length; j++) {
        var op = group.ops[j];
        if (op.cursorActivityHandlers)
          while (op.cursorActivityCalled < op.cursorActivityHandlers.length)
            op.cursorActivityHandlers[op.cursorActivityCalled++].call(null, op.cm);
      }
    } while (i < callbacks.length);
  }

  // Finish an operation, updating the display and signalling delayed events
  function endOperation(cm) {
    var op = cm.curOp, group = op.ownsGroup;
    if (!group) return;

    try { fireCallbacksForOps(group); }
    finally {
      operationGroup = null;
      for (var i = 0; i < group.ops.length; i++)
        group.ops[i].cm.curOp = null;
      endOperations(group);
    }
  }

  // The DOM updates done when an operation finishes are batched so
  // that the minimum number of relayouts are required.
  function endOperations(group) {
    var ops = group.ops;
    for (var i = 0; i < ops.length; i++) // Read DOM
      endOperation_R1(ops[i]);
    for (var i = 0; i < ops.length; i++) // Write DOM (maybe)
      endOperation_W1(ops[i]);
    for (var i = 0; i < ops.length; i++) // Read DOM
      endOperation_R2(ops[i]);
    for (var i = 0; i < ops.length; i++) // Write DOM (maybe)
      endOperation_W2(ops[i]);
    for (var i = 0; i < ops.length; i++) // Read DOM
      endOperation_finish(ops[i]);
  }

  function endOperation_R1(op) {
    var cm = op.cm, display = cm.display;
    maybeClipScrollbars(cm);
    if (op.updateMaxLine) findMaxLine(cm);

    op.mustUpdate = op.viewChanged || op.forceUpdate || op.scrollTop != null ||
      op.scrollToPos && (op.scrollToPos.from.line < display.viewFrom ||
                         op.scrollToPos.to.line >= display.viewTo) ||
      display.maxLineChanged && cm.options.lineWrapping;
    op.update = op.mustUpdate &&
      new DisplayUpdate(cm, op.mustUpdate && {top: op.scrollTop, ensure: op.scrollToPos}, op.forceUpdate);
  }

  function endOperation_W1(op) {
    op.updatedDisplay = op.mustUpdate && updateDisplayIfNeeded(op.cm, op.update);
  }

  function endOperation_R2(op) {
    var cm = op.cm, display = cm.display;
    if (op.updatedDisplay) updateHeightsInViewport(cm);

    op.barMeasure = measureForScrollbars(cm);

    // If the max line changed since it was last measured, measure it,
    // and ensure the document's width matches it.
    // updateDisplay_W2 will use these properties to do the actual resizing
    if (display.maxLineChanged && !cm.options.lineWrapping) {
      op.adjustWidthTo = measureChar(cm, display.maxLine, display.maxLine.text.length).left + 3;
      cm.display.sizerWidth = op.adjustWidthTo;
      op.barMeasure.scrollWidth =
        Math.max(display.scroller.clientWidth, display.sizer.offsetLeft + op.adjustWidthTo + scrollGap(cm) + cm.display.barWidth);
      op.maxScrollLeft = Math.max(0, display.sizer.offsetLeft + op.adjustWidthTo - displayWidth(cm));
    }

    if (op.updatedDisplay || op.selectionChanged)
      op.preparedSelection = display.input.prepareSelection(op.focus);
  }

  function endOperation_W2(op) {
    var cm = op.cm;

    if (op.adjustWidthTo != null) {
      cm.display.sizer.style.minWidth = op.adjustWidthTo + "px";
      if (op.maxScrollLeft < cm.doc.scrollLeft)
        setScrollLeft(cm, Math.min(cm.display.scroller.scrollLeft, op.maxScrollLeft), true);
      cm.display.maxLineChanged = false;
    }

    var takeFocus = op.focus && op.focus == activeElt() && (!document.hasFocus || document.hasFocus())
    if (op.preparedSelection)
      cm.display.input.showSelection(op.preparedSelection, takeFocus);
    if (op.updatedDisplay || op.startHeight != cm.doc.height)
      updateScrollbars(cm, op.barMeasure);
    if (op.updatedDisplay)
      setDocumentHeight(cm, op.barMeasure);

    if (op.selectionChanged) restartBlink(cm);

    if (cm.state.focused && op.updateInput)
      cm.display.input.reset(op.typing);
    if (takeFocus) ensureFocus(op.cm);
  }

  function endOperation_finish(op) {
    var cm = op.cm, display = cm.display, doc = cm.doc;

    if (op.updatedDisplay) postUpdateDisplay(cm, op.update);

    // Abort mouse wheel delta measurement, when scrolling explicitly
    if (display.wheelStartX != null && (op.scrollTop != null || op.scrollLeft != null || op.scrollToPos))
      display.wheelStartX = display.wheelStartY = null;

    // Propagate the scroll position to the actual DOM scroller
    if (op.scrollTop != null && (display.scroller.scrollTop != op.scrollTop || op.forceScroll)) {
      doc.scrollTop = Math.max(0, Math.min(display.scroller.scrollHeight - display.scroller.clientHeight, op.scrollTop));
      display.scrollbars.setScrollTop(doc.scrollTop);
      display.scroller.scrollTop = doc.scrollTop;
    }
    if (op.scrollLeft != null && (display.scroller.scrollLeft != op.scrollLeft || op.forceScroll)) {
      doc.scrollLeft = Math.max(0, Math.min(display.scroller.scrollWidth - display.scroller.clientWidth, op.scrollLeft));
      display.scrollbars.setScrollLeft(doc.scrollLeft);
      display.scroller.scrollLeft = doc.scrollLeft;
      alignHorizontally(cm);
    }
    // If we need to scroll a specific position into view, do so.
    if (op.scrollToPos) {
      var coords = scrollPosIntoView(cm, clipPos(doc, op.scrollToPos.from),
                                     clipPos(doc, op.scrollToPos.to), op.scrollToPos.margin);
      if (op.scrollToPos.isCursor && cm.state.focused) maybeScrollWindow(cm, coords);
    }

    // Fire events for markers that are hidden/unidden by editing or
    // undoing
    var hidden = op.maybeHiddenMarkers, unhidden = op.maybeUnhiddenMarkers;
    if (hidden) for (var i = 0; i < hidden.length; ++i)
      if (!hidden[i].lines.length) signal(hidden[i], "hide");
    if (unhidden) for (var i = 0; i < unhidden.length; ++i)
      if (unhidden[i].lines.length) signal(unhidden[i], "unhide");

    if (display.wrapper.offsetHeight)
      doc.scrollTop = cm.display.scroller.scrollTop;

    // Fire change events, and delayed event handlers
    if (op.changeObjs)
      signal(cm, "changes", cm, op.changeObjs);
    if (op.update)
      op.update.finish();
  }

  // Run the given function in an operation
  function runInOp(cm, f) {
    if (cm.curOp) return f();
    startOperation(cm);
    try { return f(); }
    finally { endOperation(cm); }
  }
  // Wraps a function in an operation. Returns the wrapped function.
  function operation(cm, f) {
    return function() {
      if (cm.curOp) return f.apply(cm, arguments);
      startOperation(cm);
      try { return f.apply(cm, arguments); }
      finally { endOperation(cm); }
    };
  }
  // Used to add methods to editor and doc instances, wrapping them in
  // operations.
  function methodOp(f) {
    return function() {
      if (this.curOp) return f.apply(this, arguments);
      startOperation(this);
      try { return f.apply(this, arguments); }
      finally { endOperation(this); }
    };
  }
  function docMethodOp(f) {
    return function() {
      var cm = this.cm;
      if (!cm || cm.curOp) return f.apply(this, arguments);
      startOperation(cm);
      try { return f.apply(this, arguments); }
      finally { endOperation(cm); }
    };
  }

  // VIEW TRACKING

  // These objects are used to represent the visible (currently drawn)
  // part of the document. A LineView may correspond to multiple
  // logical lines, if those are connected by collapsed ranges.
  function LineView(doc, line, lineN) {
    // The starting line
    this.line = line;
    // Continuing lines, if any
    this.rest = visualLineContinued(line);
    // Number of logical lines in this visual line
    this.size = this.rest ? lineNo(lst(this.rest)) - lineN + 1 : 1;
    this.node = this.text = null;
    this.hidden = lineIsHidden(doc, line);
  }

  // Create a range of LineView objects for the given lines.
  function buildViewArray(cm, from, to) {
    var array = [], nextPos;
    for (var pos = from; pos < to; pos = nextPos) {
      var view = new LineView(cm.doc, getLine(cm.doc, pos), pos);
      nextPos = pos + view.size;
      array.push(view);
    }
    return array;
  }

  // Updates the display.view data structure for a given change to the
  // document. From and to are in pre-change coordinates. Lendiff is
  // the amount of lines added or subtracted by the change. This is
  // used for changes that span multiple lines, or change the way
  // lines are divided into visual lines. regLineChange (below)
  // registers single-line changes.
  function regChange(cm, from, to, lendiff) {
    if (from == null) from = cm.doc.first;
    if (to == null) to = cm.doc.first + cm.doc.size;
    if (!lendiff) lendiff = 0;

    var display = cm.display;
    if (lendiff && to < display.viewTo &&
        (display.updateLineNumbers == null || display.updateLineNumbers > from))
      display.updateLineNumbers = from;

    cm.curOp.viewChanged = true;

    if (from >= display.viewTo) { // Change after
      if (sawCollapsedSpans && visualLineNo(cm.doc, from) < display.viewTo)
        resetView(cm);
    } else if (to <= display.viewFrom) { // Change before
      if (sawCollapsedSpans && visualLineEndNo(cm.doc, to + lendiff) > display.viewFrom) {
        resetView(cm);
      } else {
        display.viewFrom += lendiff;
        display.viewTo += lendiff;
      }
    } else if (from <= display.viewFrom && to >= display.viewTo) { // Full overlap
      resetView(cm);
    } else if (from <= display.viewFrom) { // Top overlap
      var cut = viewCuttingPoint(cm, to, to + lendiff, 1);
      if (cut) {
        display.view = display.view.slice(cut.index);
        display.viewFrom = cut.lineN;
        display.viewTo += lendiff;
      } else {
        resetView(cm);
      }
    } else if (to >= display.viewTo) { // Bottom overlap
      var cut = viewCuttingPoint(cm, from, from, -1);
      if (cut) {
        display.view = display.view.slice(0, cut.index);
        display.viewTo = cut.lineN;
      } else {
        resetView(cm);
      }
    } else { // Gap in the middle
      var cutTop = viewCuttingPoint(cm, from, from, -1);
      var cutBot = viewCuttingPoint(cm, to, to + lendiff, 1);
      if (cutTop && cutBot) {
        display.view = display.view.slice(0, cutTop.index)
          .concat(buildViewArray(cm, cutTop.lineN, cutBot.lineN))
          .concat(display.view.slice(cutBot.index));
        display.viewTo += lendiff;
      } else {
        resetView(cm);
      }
    }

    var ext = display.externalMeasured;
    if (ext) {
      if (to < ext.lineN)
        ext.lineN += lendiff;
      else if (from < ext.lineN + ext.size)
        display.externalMeasured = null;
    }
  }

  // Register a change to a single line. Type must be one of "text",
  // "gutter", "class", "widget"
  function regLineChange(cm, line, type) {
    cm.curOp.viewChanged = true;
    var display = cm.display, ext = cm.display.externalMeasured;
    if (ext && line >= ext.lineN && line < ext.lineN + ext.size)
      display.externalMeasured = null;

    if (line < display.viewFrom || line >= display.viewTo) return;
    var lineView = display.view[findViewIndex(cm, line)];
    if (lineView.node == null) return;
    var arr = lineView.changes || (lineView.changes = []);
    if (indexOf(arr, type) == -1) arr.push(type);
  }

  // Clear the view.
  function resetView(cm) {
    cm.display.viewFrom = cm.display.viewTo = cm.doc.first;
    cm.display.view = [];
    cm.display.viewOffset = 0;
  }

  // Find the view element corresponding to a given line. Return null
  // when the line isn't visible.
  function findViewIndex(cm, n) {
    if (n >= cm.display.viewTo) return null;
    n -= cm.display.viewFrom;
    if (n < 0) return null;
    var view = cm.display.view;
    for (var i = 0; i < view.length; i++) {
      n -= view[i].size;
      if (n < 0) return i;
    }
  }

  function viewCuttingPoint(cm, oldN, newN, dir) {
    var index = findViewIndex(cm, oldN), diff, view = cm.display.view;
    if (!sawCollapsedSpans || newN == cm.doc.first + cm.doc.size)
      return {index: index, lineN: newN};
    for (var i = 0, n = cm.display.viewFrom; i < index; i++)
      n += view[i].size;
    if (n != oldN) {
      if (dir > 0) {
        if (index == view.length - 1) return null;
        diff = (n + view[index].size) - oldN;
        index++;
      } else {
        diff = n - oldN;
      }
      oldN += diff; newN += diff;
    }
    while (visualLineNo(cm.doc, newN) != newN) {
      if (index == (dir < 0 ? 0 : view.length - 1)) return null;
      newN += dir * view[index - (dir < 0 ? 1 : 0)].size;
      index += dir;
    }
    return {index: index, lineN: newN};
  }

  // Force the view to cover a given range, adding empty view element
  // or clipping off existing ones as needed.
  function adjustView(cm, from, to) {
    var display = cm.display, view = display.view;
    if (view.length == 0 || from >= display.viewTo || to <= display.viewFrom) {
      display.view = buildViewArray(cm, from, to);
      display.viewFrom = from;
    } else {
      if (display.viewFrom > from)
        display.view = buildViewArray(cm, from, display.viewFrom).concat(display.view);
      else if (display.viewFrom < from)
        display.view = display.view.slice(findViewIndex(cm, from));
      display.viewFrom = from;
      if (display.viewTo < to)
        display.view = display.view.concat(buildViewArray(cm, display.viewTo, to));
      else if (display.viewTo > to)
        display.view = display.view.slice(0, findViewIndex(cm, to));
    }
    display.viewTo = to;
  }

  // Count the number of lines in the view whose DOM representation is
  // out of date (or nonexistent).
  function countDirtyView(cm) {
    var view = cm.display.view, dirty = 0;
    for (var i = 0; i < view.length; i++) {
      var lineView = view[i];
      if (!lineView.hidden && (!lineView.node || lineView.changes)) ++dirty;
    }
    return dirty;
  }

  // EVENT HANDLERS

  // Attach the necessary event handlers when initializing the editor
  function registerEventHandlers(cm) {
    var d = cm.display;
    on(d.scroller, "mousedown", operation(cm, onMouseDown));
    // Older IE's will not fire a second mousedown for a double click
    if (ie && ie_version < 11)
      on(d.scroller, "dblclick", operation(cm, function(e) {
        if (signalDOMEvent(cm, e)) return;
        var pos = posFromMouse(cm, e);
        if (!pos || clickInGutter(cm, e) || eventInWidget(cm.display, e)) return;
        e_preventDefault(e);
        var word = cm.findWordAt(pos);
        extendSelection(cm.doc, word.anchor, word.head);
      }));
    else
      on(d.scroller, "dblclick", function(e) { signalDOMEvent(cm, e) || e_preventDefault(e); });
    // Some browsers fire contextmenu *after* opening the menu, at
    // which point we can't mess with it anymore. Context menu is
    // handled in onMouseDown for these browsers.
    if (!captureRightClick) on(d.scroller, "contextmenu", function(e) {onContextMenu(cm, e);});

    // Used to suppress mouse event handling when a touch happens
    var touchFinished, prevTouch = {end: 0};
    function finishTouch() {
      if (d.activeTouch) {
        touchFinished = setTimeout(function() {d.activeTouch = null;}, 1000);
        prevTouch = d.activeTouch;
        prevTouch.end = +new Date;
      }
    };
    function isMouseLikeTouchEvent(e) {
      if (e.touches.length != 1) return false;
      var touch = e.touches[0];
      return touch.radiusX <= 1 && touch.radiusY <= 1;
    }
    function farAway(touch, other) {
      if (other.left == null) return true;
      var dx = other.left - touch.left, dy = other.top - touch.top;
      return dx * dx + dy * dy > 20 * 20;
    }
    on(d.scroller, "touchstart", function(e) {
      if (!signalDOMEvent(cm, e) && !isMouseLikeTouchEvent(e)) {
        clearTimeout(touchFinished);
        var now = +new Date;
        d.activeTouch = {start: now, moved: false,
                         prev: now - prevTouch.end <= 300 ? prevTouch : null};
        if (e.touches.length == 1) {
          d.activeTouch.left = e.touches[0].pageX;
          d.activeTouch.top = e.touches[0].pageY;
        }
      }
    });
    on(d.scroller, "touchmove", function() {
      if (d.activeTouch) d.activeTouch.moved = true;
    });
    on(d.scroller, "touchend", function(e) {
      var touch = d.activeTouch;
      if (touch && !eventInWidget(d, e) && touch.left != null &&
          !touch.moved && new Date - touch.start < 300) {
        var pos = cm.coordsChar(d.activeTouch, "page"), range;
        if (!touch.prev || farAway(touch, touch.prev)) // Single tap
          range = new Range(pos, pos);
        else if (!touch.prev.prev || farAway(touch, touch.prev.prev)) // Double tap
          range = cm.findWordAt(pos);
        else // Triple tap
          range = new Range(Pos(pos.line, 0), clipPos(cm.doc, Pos(pos.line + 1, 0)));
        cm.setSelection(range.anchor, range.head);
        cm.focus();
        e_preventDefault(e);
      }
      finishTouch();
    });
    on(d.scroller, "touchcancel", finishTouch);

    // Sync scrolling between fake scrollbars and real scrollable
    // area, ensure viewport is updated when scrolling.
    on(d.scroller, "scroll", function() {
      if (d.scroller.clientHeight) {
        setScrollTop(cm, d.scroller.scrollTop);
        setScrollLeft(cm, d.scroller.scrollLeft, true);
        signal(cm, "scroll", cm);
      }
    });

    // Listen to wheel events in order to try and update the viewport on time.
    on(d.scroller, "mousewheel", function(e){onScrollWheel(cm, e);});
    on(d.scroller, "DOMMouseScroll", function(e){onScrollWheel(cm, e);});

    // Prevent wrapper from ever scrolling
    on(d.wrapper, "scroll", function() { d.wrapper.scrollTop = d.wrapper.scrollLeft = 0; });

    d.dragFunctions = {
      enter: function(e) {if (!signalDOMEvent(cm, e)) e_stop(e);},
      over: function(e) {if (!signalDOMEvent(cm, e)) { onDragOver(cm, e); e_stop(e); }},
      start: function(e){onDragStart(cm, e);},
      drop: operation(cm, onDrop),
      leave: function(e) {if (!signalDOMEvent(cm, e)) { clearDragCursor(cm); }}
    };

    var inp = d.input.getField();
    on(inp, "keyup", function(e) { onKeyUp.call(cm, e); });
    on(inp, "keydown", operation(cm, onKeyDown));
    on(inp, "keypress", operation(cm, onKeyPress));
    on(inp, "focus", bind(onFocus, cm));
    on(inp, "blur", bind(onBlur, cm));
  }

  function dragDropChanged(cm, value, old) {
    var wasOn = old && old != CodeMirror.Init;
    if (!value != !wasOn) {
      var funcs = cm.display.dragFunctions;
      var toggle = value ? on : off;
      toggle(cm.display.scroller, "dragstart", funcs.start);
      toggle(cm.display.scroller, "dragenter", funcs.enter);
      toggle(cm.display.scroller, "dragover", funcs.over);
      toggle(cm.display.scroller, "dragleave", funcs.leave);
      toggle(cm.display.scroller, "drop", funcs.drop);
    }
  }

  // Called when the window resizes
  function onResize(cm) {
    var d = cm.display;
    if (d.lastWrapHeight == d.wrapper.clientHeight && d.lastWrapWidth == d.wrapper.clientWidth)
      return;
    // Might be a text scaling operation, clear size caches.
    d.cachedCharWidth = d.cachedTextHeight = d.cachedPaddingH = null;
    d.scrollbarsClipped = false;
    cm.setSize();
  }

  // MOUSE EVENTS

  // Return true when the given mouse event happened in a widget
  function eventInWidget(display, e) {
    for (var n = e_target(e); n != display.wrapper; n = n.parentNode) {
      if (!n || (n.nodeType == 1 && n.getAttribute("cm-ignore-events") == "true") ||
          (n.parentNode == display.sizer && n != display.mover))
        return true;
    }
  }

  // Given a mouse event, find the corresponding position. If liberal
  // is false, it checks whether a gutter or scrollbar was clicked,
  // and returns null if it was. forRect is used by rectangular
  // selections, and tries to estimate a character position even for
  // coordinates beyond the right of the text.
  function posFromMouse(cm, e, liberal, forRect) {
    var display = cm.display;
    if (!liberal && e_target(e).getAttribute("cm-not-content") == "true") return null;

    var x, y, space = display.lineSpace.getBoundingClientRect();
    // Fails unpredictably on IE[67] when mouse is dragged around quickly.
    try { x = e.clientX - space.left; y = e.clientY - space.top; }
    catch (e) { return null; }
    var coords = coordsChar(cm, x, y), line;
    if (forRect && coords.xRel == 1 && (line = getLine(cm.doc, coords.line).text).length == coords.ch) {
      var colDiff = countColumn(line, line.length, cm.options.tabSize) - line.length;
      coords = Pos(coords.line, Math.max(0, Math.round((x - paddingH(cm.display).left) / charWidth(cm.display)) - colDiff));
    }
    return coords;
  }

  // A mouse down can be a single click, double click, triple click,
  // start of selection drag, start of text drag, new cursor
  // (ctrl-click), rectangle drag (alt-drag), or xwin
  // middle-click-paste. Or it might be a click on something we should
  // not interfere with, such as a scrollbar or widget.
  function onMouseDown(e) {
    var cm = this, display = cm.display;
    if (signalDOMEvent(cm, e) || display.activeTouch && display.input.supportsTouch()) return;
    display.shift = e.shiftKey;

    if (eventInWidget(display, e)) {
      if (!webkit) {
        // Briefly turn off draggability, to allow widgets to do
        // normal dragging things.
        display.scroller.draggable = false;
        setTimeout(function(){display.scroller.draggable = true;}, 100);
      }
      return;
    }
    if (clickInGutter(cm, e)) return;
    var start = posFromMouse(cm, e);
    window.focus();

    switch (e_button(e)) {
    case 1:
      // #3261: make sure, that we're not starting a second selection
      if (cm.state.selectingText)
        cm.state.selectingText(e);
      else if (start)
        leftButtonDown(cm, e, start);
      else if (e_target(e) == display.scroller)
        e_preventDefault(e);
      break;
    case 2:
      if (webkit) cm.state.lastMiddleDown = +new Date;
      if (start) extendSelection(cm.doc, start);
      setTimeout(function() {display.input.focus();}, 20);
      e_preventDefault(e);
      break;
    case 3:
      if (captureRightClick) onContextMenu(cm, e);
      else delayBlurEvent(cm);
      break;
    }
  }

  var lastClick, lastDoubleClick;
  function leftButtonDown(cm, e, start) {
    if (ie) setTimeout(bind(ensureFocus, cm), 0);
    else cm.curOp.focus = activeElt();

    var now = +new Date, type;
    if (lastDoubleClick && lastDoubleClick.time > now - 400 && cmp(lastDoubleClick.pos, start) == 0) {
      type = "triple";
    } else if (lastClick && lastClick.time > now - 400 && cmp(lastClick.pos, start) == 0) {
      type = "double";
      lastDoubleClick = {time: now, pos: start};
    } else {
      type = "single";
      lastClick = {time: now, pos: start};
    }

    var sel = cm.doc.sel, modifier = mac ? e.metaKey : e.ctrlKey, contained;
    if (cm.options.dragDrop && dragAndDrop && !cm.isReadOnly() &&
        type == "single" && (contained = sel.contains(start)) > -1 &&
        (cmp((contained = sel.ranges[contained]).from(), start) < 0 || start.xRel > 0) &&
        (cmp(contained.to(), start) > 0 || start.xRel < 0))
      leftButtonStartDrag(cm, e, start, modifier);
    else
      leftButtonSelect(cm, e, start, type, modifier);
  }

  // Start a text drag. When it ends, see if any dragging actually
  // happen, and treat as a click if it didn't.
  function leftButtonStartDrag(cm, e, start, modifier) {
    var display = cm.display, startTime = +new Date;
    var dragEnd = operation(cm, function(e2) {
      if (webkit) display.scroller.draggable = false;
      cm.state.draggingText = false;
      off(document, "mouseup", dragEnd);
      off(display.scroller, "drop", dragEnd);
      if (Math.abs(e.clientX - e2.clientX) + Math.abs(e.clientY - e2.clientY) < 10) {
        e_preventDefault(e2);
        if (!modifier && +new Date - 200 < startTime)
          extendSelection(cm.doc, start);
        // Work around unexplainable focus problem in IE9 (#2127) and Chrome (#3081)
        if (webkit || ie && ie_version == 9)
          setTimeout(function() {document.body.focus(); display.input.focus();}, 20);
        else
          display.input.focus();
      }
    });
    // Let the drag handler handle this.
    if (webkit) display.scroller.draggable = true;
    cm.state.draggingText = dragEnd;
    dragEnd.copy = mac ? e.altKey : e.ctrlKey
    // IE's approach to draggable
    if (display.scroller.dragDrop) display.scroller.dragDrop();
    on(document, "mouseup", dragEnd);
    on(display.scroller, "drop", dragEnd);
  }

  // Normal selection, as opposed to text dragging.
  function leftButtonSelect(cm, e, start, type, addNew) {
    var display = cm.display, doc = cm.doc;
    e_preventDefault(e);

    var ourRange, ourIndex, startSel = doc.sel, ranges = startSel.ranges;
    if (addNew && !e.shiftKey) {
      ourIndex = doc.sel.contains(start);
      if (ourIndex > -1)
        ourRange = ranges[ourIndex];
      else
        ourRange = new Range(start, start);
    } else {
      ourRange = doc.sel.primary();
      ourIndex = doc.sel.primIndex;
    }

    if (chromeOS ? e.shiftKey && e.metaKey : e.altKey) {
      type = "rect";
      if (!addNew) ourRange = new Range(start, start);
      start = posFromMouse(cm, e, true, true);
      ourIndex = -1;
    } else if (type == "double") {
      var word = cm.findWordAt(start);
      if (cm.display.shift || doc.extend)
        ourRange = extendRange(doc, ourRange, word.anchor, word.head);
      else
        ourRange = word;
    } else if (type == "triple") {
      var line = new Range(Pos(start.line, 0), clipPos(doc, Pos(start.line + 1, 0)));
      if (cm.display.shift || doc.extend)
        ourRange = extendRange(doc, ourRange, line.anchor, line.head);
      else
        ourRange = line;
    } else {
      ourRange = extendRange(doc, ourRange, start);
    }

    if (!addNew) {
      ourIndex = 0;
      setSelection(doc, new Selection([ourRange], 0), sel_mouse);
      startSel = doc.sel;
    } else if (ourIndex == -1) {
      ourIndex = ranges.length;
      setSelection(doc, normalizeSelection(ranges.concat([ourRange]), ourIndex),
                   {scroll: false, origin: "*mouse"});
    } else if (ranges.length > 1 && ranges[ourIndex].empty() && type == "single" && !e.shiftKey) {
      setSelection(doc, normalizeSelection(ranges.slice(0, ourIndex).concat(ranges.slice(ourIndex + 1)), 0),
                   {scroll: false, origin: "*mouse"});
      startSel = doc.sel;
    } else {
      replaceOneSelection(doc, ourIndex, ourRange, sel_mouse);
    }

    var lastPos = start;
    function extendTo(pos) {
      if (cmp(lastPos, pos) == 0) return;
      lastPos = pos;

      if (type == "rect") {
        var ranges = [], tabSize = cm.options.tabSize;
        var startCol = countColumn(getLine(doc, start.line).text, start.ch, tabSize);
        var posCol = countColumn(getLine(doc, pos.line).text, pos.ch, tabSize);
        var left = Math.min(startCol, posCol), right = Math.max(startCol, posCol);
        for (var line = Math.min(start.line, pos.line), end = Math.min(cm.lastLine(), Math.max(start.line, pos.line));
             line <= end; line++) {
          var text = getLine(doc, line).text, leftPos = findColumn(text, left, tabSize);
          if (left == right)
            ranges.push(new Range(Pos(line, leftPos), Pos(line, leftPos)));
          else if (text.length > leftPos)
            ranges.push(new Range(Pos(line, leftPos), Pos(line, findColumn(text, right, tabSize))));
        }
        if (!ranges.length) ranges.push(new Range(start, start));
        setSelection(doc, normalizeSelection(startSel.ranges.slice(0, ourIndex).concat(ranges), ourIndex),
                     {origin: "*mouse", scroll: false});
        cm.scrollIntoView(pos);
      } else {
        var oldRange = ourRange;
        var anchor = oldRange.anchor, head = pos;
        if (type != "single") {
          if (type == "double")
            var range = cm.findWordAt(pos);
          else
            var range = new Range(Pos(pos.line, 0), clipPos(doc, Pos(pos.line + 1, 0)));
          if (cmp(range.anchor, anchor) > 0) {
            head = range.head;
            anchor = minPos(oldRange.from(), range.anchor);
          } else {
            head = range.anchor;
            anchor = maxPos(oldRange.to(), range.head);
          }
        }
        var ranges = startSel.ranges.slice(0);
        ranges[ourIndex] = new Range(clipPos(doc, anchor), head);
        setSelection(doc, normalizeSelection(ranges, ourIndex), sel_mouse);
      }
    }

    var editorSize = display.wrapper.getBoundingClientRect();
    // Used to ensure timeout re-tries don't fire when another extend
    // happened in the meantime (clearTimeout isn't reliable -- at
    // least on Chrome, the timeouts still happen even when cleared,
    // if the clear happens after their scheduled firing time).
    var counter = 0;

    function extend(e) {
      var curCount = ++counter;
      var cur = posFromMouse(cm, e, true, type == "rect");
      if (!cur) return;
      if (cmp(cur, lastPos) != 0) {
        cm.curOp.focus = activeElt();
        extendTo(cur);
        var visible = visibleLines(display, doc);
        if (cur.line >= visible.to || cur.line < visible.from)
          setTimeout(operation(cm, function(){if (counter == curCount) extend(e);}), 150);
      } else {
        var outside = e.clientY < editorSize.top ? -20 : e.clientY > editorSize.bottom ? 20 : 0;
        if (outside) setTimeout(operation(cm, function() {
          if (counter != curCount) return;
          display.scroller.scrollTop += outside;
          extend(e);
        }), 50);
      }
    }

    function done(e) {
      cm.state.selectingText = false;
      counter = Infinity;
      e_preventDefault(e);
      display.input.focus();
      off(document, "mousemove", move);
      off(document, "mouseup", up);
      doc.history.lastSelOrigin = null;
    }

    var move = operation(cm, function(e) {
      if (!e_button(e)) done(e);
      else extend(e);
    });
    var up = operation(cm, done);
    cm.state.selectingText = up;
    on(document, "mousemove", move);
    on(document, "mouseup", up);
  }

  // Determines whether an event happened in the gutter, and fires the
  // handlers for the corresponding event.
  function gutterEvent(cm, e, type, prevent) {
    try { var mX = e.clientX, mY = e.clientY; }
    catch(e) { return false; }
    if (mX >= Math.floor(cm.display.gutters.getBoundingClientRect().right)) return false;
    if (prevent) e_preventDefault(e);

    var display = cm.display;
    var lineBox = display.lineDiv.getBoundingClientRect();

    if (mY > lineBox.bottom || !hasHandler(cm, type)) return e_defaultPrevented(e);
    mY -= lineBox.top - display.viewOffset;

    for (var i = 0; i < cm.options.gutters.length; ++i) {
      var g = display.gutters.childNodes[i];
      if (g && g.getBoundingClientRect().right >= mX) {
        var line = lineAtHeight(cm.doc, mY);
        var gutter = cm.options.gutters[i];
        signal(cm, type, cm, line, gutter, e);
        return e_defaultPrevented(e);
      }
    }
  }

  function clickInGutter(cm, e) {
    return gutterEvent(cm, e, "gutterClick", true);
  }

  // Kludge to work around strange IE behavior where it'll sometimes
  // re-fire a series of drag-related events right after the drop (#1551)
  var lastDrop = 0;

  function onDrop(e) {
    var cm = this;
    clearDragCursor(cm);
    if (signalDOMEvent(cm, e) || eventInWidget(cm.display, e))
      return;
    e_preventDefault(e);
    if (ie) lastDrop = +new Date;
    var pos = posFromMouse(cm, e, true), files = e.dataTransfer.files;
    if (!pos || cm.isReadOnly()) return;
    // Might be a file drop, in which case we simply extract the text
    // and insert it.
    if (files && files.length && window.FileReader && window.File) {
      var n = files.length, text = Array(n), read = 0;
      var loadFile = function(file, i) {
        if (cm.options.allowDropFileTypes &&
            indexOf(cm.options.allowDropFileTypes, file.type) == -1)
          return;

        var reader = new FileReader;
        reader.onload = operation(cm, function() {
          var content = reader.result;
          if (/[\x00-\x08\x0e-\x1f]{2}/.test(content)) content = "";
          text[i] = content;
          if (++read == n) {
            pos = clipPos(cm.doc, pos);
            var change = {from: pos, to: pos,
                          text: cm.doc.splitLines(text.join(cm.doc.lineSeparator())),
                          origin: "paste"};
            makeChange(cm.doc, change);
            setSelectionReplaceHistory(cm.doc, simpleSelection(pos, changeEnd(change)));
          }
        });
        reader.readAsText(file);
      };
      for (var i = 0; i < n; ++i) loadFile(files[i], i);
    } else { // Normal drop
      // Don't do a replace if the drop happened inside of the selected text.
      if (cm.state.draggingText && cm.doc.sel.contains(pos) > -1) {
        cm.state.draggingText(e);
        // Ensure the editor is re-focused
        setTimeout(function() {cm.display.input.focus();}, 20);
        return;
      }
      try {
        var text = e.dataTransfer.getData("Text");
        if (text) {
          if (cm.state.draggingText && !cm.state.draggingText.copy)
            var selected = cm.listSelections();
          setSelectionNoUndo(cm.doc, simpleSelection(pos, pos));
          if (selected) for (var i = 0; i < selected.length; ++i)
            replaceRange(cm.doc, "", selected[i].anchor, selected[i].head, "drag");
          cm.replaceSelection(text, "around", "paste");
          cm.display.input.focus();
        }
      }
      catch(e){}
    }
  }

  function onDragStart(cm, e) {
    if (ie && (!cm.state.draggingText || +new Date - lastDrop < 100)) { e_stop(e); return; }
    if (signalDOMEvent(cm, e) || eventInWidget(cm.display, e)) return;

    e.dataTransfer.setData("Text", cm.getSelection());
    e.dataTransfer.effectAllowed = "copyMove"

    // Use dummy image instead of default browsers image.
    // Recent Safari (~6.0.2) have a tendency to segfault when this happens, so we don't do it there.
    if (e.dataTransfer.setDragImage && !safari) {
      var img = elt("img", null, null, "position: fixed; left: 0; top: 0;");
      img.src = "data:image/gif;base64,R0lGODlhAQABAAAAACH5BAEKAAEALAAAAAABAAEAAAICTAEAOw==";
      if (presto) {
        img.width = img.height = 1;
        cm.display.wrapper.appendChild(img);
        // Force a relayout, or Opera won't use our image for some obscure reason
        img._top = img.offsetTop;
      }
      e.dataTransfer.setDragImage(img, 0, 0);
      if (presto) img.parentNode.removeChild(img);
    }
  }

  function onDragOver(cm, e) {
    var pos = posFromMouse(cm, e);
    if (!pos) return;
    var frag = document.createDocumentFragment();
    drawSelectionCursor(cm, pos, frag);
    if (!cm.display.dragCursor) {
      cm.display.dragCursor = elt("div", null, "CodeMirror-cursors CodeMirror-dragcursors");
      cm.display.lineSpace.insertBefore(cm.display.dragCursor, cm.display.cursorDiv);
    }
    removeChildrenAndAdd(cm.display.dragCursor, frag);
  }

  function clearDragCursor(cm) {
    if (cm.display.dragCursor) {
      cm.display.lineSpace.removeChild(cm.display.dragCursor);
      cm.display.dragCursor = null;
    }
  }

  // SCROLL EVENTS

  // Sync the scrollable area and scrollbars, ensure the viewport
  // covers the visible area.
  function setScrollTop(cm, val) {
    if (Math.abs(cm.doc.scrollTop - val) < 2) return;
    cm.doc.scrollTop = val;
    if (!gecko) updateDisplaySimple(cm, {top: val});
    if (cm.display.scroller.scrollTop != val) cm.display.scroller.scrollTop = val;
    cm.display.scrollbars.setScrollTop(val);
    if (gecko) updateDisplaySimple(cm);
    startWorker(cm, 100);
  }
  // Sync scroller and scrollbar, ensure the gutter elements are
  // aligned.
  function setScrollLeft(cm, val, isScroller) {
    if (isScroller ? val == cm.doc.scrollLeft : Math.abs(cm.doc.scrollLeft - val) < 2) return;
    val = Math.min(val, cm.display.scroller.scrollWidth - cm.display.scroller.clientWidth);
    cm.doc.scrollLeft = val;
    alignHorizontally(cm);
    if (cm.display.scroller.scrollLeft != val) cm.display.scroller.scrollLeft = val;
    cm.display.scrollbars.setScrollLeft(val);
  }

  // Since the delta values reported on mouse wheel events are
  // unstandardized between browsers and even browser versions, and
  // generally horribly unpredictable, this code starts by measuring
  // the scroll effect that the first few mouse wheel events have,
  // and, from that, detects the way it can convert deltas to pixel
  // offsets afterwards.
  //
  // The reason we want to know the amount a wheel event will scroll
  // is that it gives us a chance to update the display before the
  // actual scrolling happens, reducing flickering.

  var wheelSamples = 0, wheelPixelsPerUnit = null;
  // Fill in a browser-detected starting value on browsers where we
  // know one. These don't have to be accurate -- the result of them
  // being wrong would just be a slight flicker on the first wheel
  // scroll (if it is large enough).
  if (ie) wheelPixelsPerUnit = -.53;
  else if (gecko) wheelPixelsPerUnit = 15;
  else if (chrome) wheelPixelsPerUnit = -.7;
  else if (safari) wheelPixelsPerUnit = -1/3;

  var wheelEventDelta = function(e) {
    var dx = e.wheelDeltaX, dy = e.wheelDeltaY;
    if (dx == null && e.detail && e.axis == e.HORIZONTAL_AXIS) dx = e.detail;
    if (dy == null && e.detail && e.axis == e.VERTICAL_AXIS) dy = e.detail;
    else if (dy == null) dy = e.wheelDelta;
    return {x: dx, y: dy};
  };
  CodeMirror.wheelEventPixels = function(e) {
    var delta = wheelEventDelta(e);
    delta.x *= wheelPixelsPerUnit;
    delta.y *= wheelPixelsPerUnit;
    return delta;
  };

  function onScrollWheel(cm, e) {
    var delta = wheelEventDelta(e), dx = delta.x, dy = delta.y;

    var display = cm.display, scroll = display.scroller;
    // Quit if there's nothing to scroll here
    var canScrollX = scroll.scrollWidth > scroll.clientWidth;
    var canScrollY = scroll.scrollHeight > scroll.clientHeight;
    if (!(dx && canScrollX || dy && canScrollY)) return;

    // Webkit browsers on OS X abort momentum scrolls when the target
    // of the scroll event is removed from the scrollable element.
    // This hack (see related code in patchDisplay) makes sure the
    // element is kept around.
    if (dy && mac && webkit) {
      outer: for (var cur = e.target, view = display.view; cur != scroll; cur = cur.parentNode) {
        for (var i = 0; i < view.length; i++) {
          if (view[i].node == cur) {
            cm.display.currentWheelTarget = cur;
            break outer;
          }
        }
      }
    }

    // On some browsers, horizontal scrolling will cause redraws to
    // happen before the gutter has been realigned, causing it to
    // wriggle around in a most unseemly way. When we have an
    // estimated pixels/delta value, we just handle horizontal
    // scrolling entirely here. It'll be slightly off from native, but
    // better than glitching out.
    if (dx && !gecko && !presto && wheelPixelsPerUnit != null) {
      if (dy && canScrollY)
        setScrollTop(cm, Math.max(0, Math.min(scroll.scrollTop + dy * wheelPixelsPerUnit, scroll.scrollHeight - scroll.clientHeight)));
      setScrollLeft(cm, Math.max(0, Math.min(scroll.scrollLeft + dx * wheelPixelsPerUnit, scroll.scrollWidth - scroll.clientWidth)));
      // Only prevent default scrolling if vertical scrolling is
      // actually possible. Otherwise, it causes vertical scroll
      // jitter on OSX trackpads when deltaX is small and deltaY
      // is large (issue #3579)
      if (!dy || (dy && canScrollY))
        e_preventDefault(e);
      display.wheelStartX = null; // Abort measurement, if in progress
      return;
    }

    // 'Project' the visible viewport to cover the area that is being
    // scrolled into view (if we know enough to estimate it).
    if (dy && wheelPixelsPerUnit != null) {
      var pixels = dy * wheelPixelsPerUnit;
      var top = cm.doc.scrollTop, bot = top + display.wrapper.clientHeight;
      if (pixels < 0) top = Math.max(0, top + pixels - 50);
      else bot = Math.min(cm.doc.height, bot + pixels + 50);
      updateDisplaySimple(cm, {top: top, bottom: bot});
    }

    if (wheelSamples < 20) {
      if (display.wheelStartX == null) {
        display.wheelStartX = scroll.scrollLeft; display.wheelStartY = scroll.scrollTop;
        display.wheelDX = dx; display.wheelDY = dy;
        setTimeout(function() {
          if (display.wheelStartX == null) return;
          var movedX = scroll.scrollLeft - display.wheelStartX;
          var movedY = scroll.scrollTop - display.wheelStartY;
          var sample = (movedY && display.wheelDY && movedY / display.wheelDY) ||
            (movedX && display.wheelDX && movedX / display.wheelDX);
          display.wheelStartX = display.wheelStartY = null;
          if (!sample) return;
          wheelPixelsPerUnit = (wheelPixelsPerUnit * wheelSamples + sample) / (wheelSamples + 1);
          ++wheelSamples;
        }, 200);
      } else {
        display.wheelDX += dx; display.wheelDY += dy;
      }
    }
  }

  // KEY EVENTS

  // Run a handler that was bound to a key.
  function doHandleBinding(cm, bound, dropShift) {
    if (typeof bound == "string") {
      bound = commands[bound];
      if (!bound) return false;
    }
    // Ensure previous input has been read, so that the handler sees a
    // consistent view of the document
    cm.display.input.ensurePolled();
    var prevShift = cm.display.shift, done = false;
    try {
      if (cm.isReadOnly()) cm.state.suppressEdits = true;
      if (dropShift) cm.display.shift = false;
      done = bound(cm) != Pass;
    } finally {
      cm.display.shift = prevShift;
      cm.state.suppressEdits = false;
    }
    return done;
  }

  function lookupKeyForEditor(cm, name, handle) {
    for (var i = 0; i < cm.state.keyMaps.length; i++) {
      var result = lookupKey(name, cm.state.keyMaps[i], handle, cm);
      if (result) return result;
    }
    return (cm.options.extraKeys && lookupKey(name, cm.options.extraKeys, handle, cm))
      || lookupKey(name, cm.options.keyMap, handle, cm);
  }

  var stopSeq = new Delayed;
  function dispatchKey(cm, name, e, handle) {
    var seq = cm.state.keySeq;
    if (seq) {
      if (isModifierKey(name)) return "handled";
      stopSeq.set(50, function() {
        if (cm.state.keySeq == seq) {
          cm.state.keySeq = null;
          cm.display.input.reset();
        }
      });
      name = seq + " " + name;
    }
    var result = lookupKeyForEditor(cm, name, handle);

    if (result == "multi")
      cm.state.keySeq = name;
    if (result == "handled")
      signalLater(cm, "keyHandled", cm, name, e);

    if (result == "handled" || result == "multi") {
      e_preventDefault(e);
      restartBlink(cm);
    }

    if (seq && !result && /\'$/.test(name)) {
      e_preventDefault(e);
      return true;
    }
    return !!result;
  }

  // Handle a key from the keydown event.
  function handleKeyBinding(cm, e) {
    var name = keyName(e, true);
    if (!name) return false;

    if (e.shiftKey && !cm.state.keySeq) {
      // First try to resolve full name (including 'Shift-'). Failing
      // that, see if there is a cursor-motion command (starting with
      // 'go') bound to the keyname without 'Shift-'.
      return dispatchKey(cm, "Shift-" + name, e, function(b) {return doHandleBinding(cm, b, true);})
          || dispatchKey(cm, name, e, function(b) {
               if (typeof b == "string" ? /^go[A-Z]/.test(b) : b.motion)
                 return doHandleBinding(cm, b);
             });
    } else {
      return dispatchKey(cm, name, e, function(b) { return doHandleBinding(cm, b); });
    }
  }

  // Handle a key from the keypress event
  function handleCharBinding(cm, e, ch) {
    return dispatchKey(cm, "'" + ch + "'", e,
                       function(b) { return doHandleBinding(cm, b, true); });
  }

  var lastStoppedKey = null;
  function onKeyDown(e) {
    var cm = this;
    cm.curOp.focus = activeElt();
    if (signalDOMEvent(cm, e)) return;
    // IE does strange things with escape.
    if (ie && ie_version < 11 && e.keyCode == 27) e.returnValue = false;
    var code = e.keyCode;
    cm.display.shift = code == 16 || e.shiftKey;
    var handled = handleKeyBinding(cm, e);
    if (presto) {
      lastStoppedKey = handled ? code : null;
      // Opera has no cut event... we try to at least catch the key combo
      if (!handled && code == 88 && !hasCopyEvent && (mac ? e.metaKey : e.ctrlKey))
        cm.replaceSelection("", null, "cut");
    }

    // Turn mouse into crosshair when Alt is held on Mac.
    if (code == 18 && !/\bCodeMirror-crosshair\b/.test(cm.display.lineDiv.className))
      showCrossHair(cm);
  }

  function showCrossHair(cm) {
    var lineDiv = cm.display.lineDiv;
    addClass(lineDiv, "CodeMirror-crosshair");

    function up(e) {
      if (e.keyCode == 18 || !e.altKey) {
        rmClass(lineDiv, "CodeMirror-crosshair");
        off(document, "keyup", up);
        off(document, "mouseover", up);
      }
    }
    on(document, "keyup", up);
    on(document, "mouseover", up);
  }

  function onKeyUp(e) {
    if (e.keyCode == 16) this.doc.sel.shift = false;
    signalDOMEvent(this, e);
  }

  function onKeyPress(e) {
    var cm = this;
    if (eventInWidget(cm.display, e) || signalDOMEvent(cm, e) || e.ctrlKey && !e.altKey || mac && e.metaKey) return;
    var keyCode = e.keyCode, charCode = e.charCode;
    if (presto && keyCode == lastStoppedKey) {lastStoppedKey = null; e_preventDefault(e); return;}
    if ((presto && (!e.which || e.which < 10)) && handleKeyBinding(cm, e)) return;
    var ch = String.fromCharCode(charCode == null ? keyCode : charCode);
    if (handleCharBinding(cm, e, ch)) return;
    cm.display.input.onKeyPress(e);
  }

  // FOCUS/BLUR EVENTS

  function delayBlurEvent(cm) {
    cm.state.delayingBlurEvent = true;
    setTimeout(function() {
      if (cm.state.delayingBlurEvent) {
        cm.state.delayingBlurEvent = false;
        onBlur(cm);
      }
    }, 100);
  }

  function onFocus(cm) {
    if (cm.state.delayingBlurEvent) cm.state.delayingBlurEvent = false;

    if (cm.options.readOnly == "nocursor") return;
    if (!cm.state.focused) {
      signal(cm, "focus", cm);
      cm.state.focused = true;
      addClass(cm.display.wrapper, "CodeMirror-focused");
      // This test prevents this from firing when a context
      // menu is closed (since the input reset would kill the
      // select-all detection hack)
      if (!cm.curOp && cm.display.selForContextMenu != cm.doc.sel) {
        cm.display.input.reset();
        if (webkit) setTimeout(function() { cm.display.input.reset(true); }, 20); // Issue #1730
      }
      cm.display.input.receivedFocus();
    }
    restartBlink(cm);
  }
  function onBlur(cm) {
    if (cm.state.delayingBlurEvent) return;

    if (cm.state.focused) {
      signal(cm, "blur", cm);
      cm.state.focused = false;
      rmClass(cm.display.wrapper, "CodeMirror-focused");
    }
    clearInterval(cm.display.blinker);
    setTimeout(function() {if (!cm.state.focused) cm.display.shift = false;}, 150);
  }

  // CONTEXT MENU HANDLING

  // To make the context menu work, we need to briefly unhide the
  // textarea (making it as unobtrusive as possible) to let the
  // right-click take effect on it.
  function onContextMenu(cm, e) {
    if (eventInWidget(cm.display, e) || contextMenuInGutter(cm, e)) return;
    if (signalDOMEvent(cm, e, "contextmenu")) return;
    cm.display.input.onContextMenu(e);
  }

  function contextMenuInGutter(cm, e) {
    if (!hasHandler(cm, "gutterContextMenu")) return false;
    return gutterEvent(cm, e, "gutterContextMenu", false);
  }

  // UPDATING

  // Compute the position of the end of a change (its 'to' property
  // refers to the pre-change end).
  var changeEnd = CodeMirror.changeEnd = function(change) {
    if (!change.text) return change.to;
    return Pos(change.from.line + change.text.length - 1,
               lst(change.text).length + (change.text.length == 1 ? change.from.ch : 0));
  };

  // Adjust a position to refer to the post-change position of the
  // same text, or the end of the change if the change covers it.
  function adjustForChange(pos, change) {
    if (cmp(pos, change.from) < 0) return pos;
    if (cmp(pos, change.to) <= 0) return changeEnd(change);

    var line = pos.line + change.text.length - (change.to.line - change.from.line) - 1, ch = pos.ch;
    if (pos.line == change.to.line) ch += changeEnd(change).ch - change.to.ch;
    return Pos(line, ch);
  }

  function computeSelAfterChange(doc, change) {
    var out = [];
    for (var i = 0; i < doc.sel.ranges.length; i++) {
      var range = doc.sel.ranges[i];
      out.push(new Range(adjustForChange(range.anchor, change),
                         adjustForChange(range.head, change)));
    }
    return normalizeSelection(out, doc.sel.primIndex);
  }

  function offsetPos(pos, old, nw) {
    if (pos.line == old.line)
      return Pos(nw.line, pos.ch - old.ch + nw.ch);
    else
      return Pos(nw.line + (pos.line - old.line), pos.ch);
  }

  // Used by replaceSelections to allow moving the selection to the
  // start or around the replaced test. Hint may be "start" or "around".
  function computeReplacedSel(doc, changes, hint) {
    var out = [];
    var oldPrev = Pos(doc.first, 0), newPrev = oldPrev;
    for (var i = 0; i < changes.length; i++) {
      var change = changes[i];
      var from = offsetPos(change.from, oldPrev, newPrev);
      var to = offsetPos(changeEnd(change), oldPrev, newPrev);
      oldPrev = change.to;
      newPrev = to;
      if (hint == "around") {
        var range = doc.sel.ranges[i], inv = cmp(range.head, range.anchor) < 0;
        out[i] = new Range(inv ? to : from, inv ? from : to);
      } else {
        out[i] = new Range(from, from);
      }
    }
    return new Selection(out, doc.sel.primIndex);
  }

  // Allow "beforeChange" event handlers to influence a change
  function filterChange(doc, change, update) {
    var obj = {
      canceled: false,
      from: change.from,
      to: change.to,
      text: change.text,
      origin: change.origin,
      cancel: function() { this.canceled = true; }
    };
    if (update) obj.update = function(from, to, text, origin) {
      if (from) this.from = clipPos(doc, from);
      if (to) this.to = clipPos(doc, to);
      if (text) this.text = text;
      if (origin !== undefined) this.origin = origin;
    };
    signal(doc, "beforeChange", doc, obj);
    if (doc.cm) signal(doc.cm, "beforeChange", doc.cm, obj);

    if (obj.canceled) return null;
    return {from: obj.from, to: obj.to, text: obj.text, origin: obj.origin};
  }

  // Apply a change to a document, and add it to the document's
  // history, and propagating it to all linked documents.
  function makeChange(doc, change, ignoreReadOnly) {
    if (doc.cm) {
      if (!doc.cm.curOp) return operation(doc.cm, makeChange)(doc, change, ignoreReadOnly);
      if (doc.cm.state.suppressEdits) return;
    }

    if (hasHandler(doc, "beforeChange") || doc.cm && hasHandler(doc.cm, "beforeChange")) {
      change = filterChange(doc, change, true);
      if (!change) return;
    }

    // Possibly split or suppress the update based on the presence
    // of read-only spans in its range.
    var split = sawReadOnlySpans && !ignoreReadOnly && removeReadOnlyRanges(doc, change.from, change.to);
    if (split) {
      for (var i = split.length - 1; i >= 0; --i)
        makeChangeInner(doc, {from: split[i].from, to: split[i].to, text: i ? [""] : change.text});
    } else {
      makeChangeInner(doc, change);
    }
  }

  function makeChangeInner(doc, change) {
    if (change.text.length == 1 && change.text[0] == "" && cmp(change.from, change.to) == 0) return;
    var selAfter = computeSelAfterChange(doc, change);
    addChangeToHistory(doc, change, selAfter, doc.cm ? doc.cm.curOp.id : NaN);

    makeChangeSingleDoc(doc, change, selAfter, stretchSpansOverChange(doc, change));
    var rebased = [];

    linkedDocs(doc, function(doc, sharedHist) {
      if (!sharedHist && indexOf(rebased, doc.history) == -1) {
        rebaseHist(doc.history, change);
        rebased.push(doc.history);
      }
      makeChangeSingleDoc(doc, change, null, stretchSpansOverChange(doc, change));
    });
  }

  // Revert a change stored in a document's history.
  function makeChangeFromHistory(doc, type, allowSelectionOnly) {
    if (doc.cm && doc.cm.state.suppressEdits) return;

    var hist = doc.history, event, selAfter = doc.sel;
    var source = type == "undo" ? hist.done : hist.undone, dest = type == "undo" ? hist.undone : hist.done;

    // Verify that there is a useable event (so that ctrl-z won't
    // needlessly clear selection events)
    for (var i = 0; i < source.length; i++) {
      event = source[i];
      if (allowSelectionOnly ? event.ranges && !event.equals(doc.sel) : !event.ranges)
        break;
    }
    if (i == source.length) return;
    hist.lastOrigin = hist.lastSelOrigin = null;

    for (;;) {
      event = source.pop();
      if (event.ranges) {
        pushSelectionToHistory(event, dest);
        if (allowSelectionOnly && !event.equals(doc.sel)) {
          setSelection(doc, event, {clearRedo: false});
          return;
        }
        selAfter = event;
      }
      else break;
    }

    // Build up a reverse change object to add to the opposite history
    // stack (redo when undoing, and vice versa).
    var antiChanges = [];
    pushSelectionToHistory(selAfter, dest);
    dest.push({changes: antiChanges, generation: hist.generation});
    hist.generation = event.generation || ++hist.maxGeneration;

    var filter = hasHandler(doc, "beforeChange") || doc.cm && hasHandler(doc.cm, "beforeChange");

    for (var i = event.changes.length - 1; i >= 0; --i) {
      var change = event.changes[i];
      change.origin = type;
      if (filter && !filterChange(doc, change, false)) {
        source.length = 0;
        return;
      }

      antiChanges.push(historyChangeFromChange(doc, change));

      var after = i ? computeSelAfterChange(doc, change) : lst(source);
      makeChangeSingleDoc(doc, change, after, mergeOldSpans(doc, change));
      if (!i && doc.cm) doc.cm.scrollIntoView({from: change.from, to: changeEnd(change)});
      var rebased = [];

      // Propagate to the linked documents
      linkedDocs(doc, function(doc, sharedHist) {
        if (!sharedHist && indexOf(rebased, doc.history) == -1) {
          rebaseHist(doc.history, change);
          rebased.push(doc.history);
        }
        makeChangeSingleDoc(doc, change, null, mergeOldSpans(doc, change));
      });
    }
  }

  // Sub-views need their line numbers shifted when text is added
  // above or below them in the parent document.
  function shiftDoc(doc, distance) {
    if (distance == 0) return;
    doc.first += distance;
    doc.sel = new Selection(map(doc.sel.ranges, function(range) {
      return new Range(Pos(range.anchor.line + distance, range.anchor.ch),
                       Pos(range.head.line + distance, range.head.ch));
    }), doc.sel.primIndex);
    if (doc.cm) {
      regChange(doc.cm, doc.first, doc.first - distance, distance);
      for (var d = doc.cm.display, l = d.viewFrom; l < d.viewTo; l++)
        regLineChange(doc.cm, l, "gutter");
    }
  }

  // More lower-level change function, handling only a single document
  // (not linked ones).
  function makeChangeSingleDoc(doc, change, selAfter, spans) {
    if (doc.cm && !doc.cm.curOp)
      return operation(doc.cm, makeChangeSingleDoc)(doc, change, selAfter, spans);

    if (change.to.line < doc.first) {
      shiftDoc(doc, change.text.length - 1 - (change.to.line - change.from.line));
      return;
    }
    if (change.from.line > doc.lastLine()) return;

    // Clip the change to the size of this doc
    if (change.from.line < doc.first) {
      var shift = change.text.length - 1 - (doc.first - change.from.line);
      shiftDoc(doc, shift);
      change = {from: Pos(doc.first, 0), to: Pos(change.to.line + shift, change.to.ch),
                text: [lst(change.text)], origin: change.origin};
    }
    var last = doc.lastLine();
    if (change.to.line > last) {
      change = {from: change.from, to: Pos(last, getLine(doc, last).text.length),
                text: [change.text[0]], origin: change.origin};
    }

    change.removed = getBetween(doc, change.from, change.to);

    if (!selAfter) selAfter = computeSelAfterChange(doc, change);
    if (doc.cm) makeChangeSingleDocInEditor(doc.cm, change, spans);
    else updateDoc(doc, change, spans);
    setSelectionNoUndo(doc, selAfter, sel_dontScroll);
  }

  // Handle the interaction of a change to a document with the editor
  // that this document is part of.
  function makeChangeSingleDocInEditor(cm, change, spans) {
    var doc = cm.doc, display = cm.display, from = change.from, to = change.to;

    var recomputeMaxLength = false, checkWidthStart = from.line;
    if (!cm.options.lineWrapping) {
      checkWidthStart = lineNo(visualLine(getLine(doc, from.line)));
      doc.iter(checkWidthStart, to.line + 1, function(line) {
        if (line == display.maxLine) {
          recomputeMaxLength = true;
          return true;
        }
      });
    }

    if (doc.sel.contains(change.from, change.to) > -1)
      signalCursorActivity(cm);

    updateDoc(doc, change, spans, estimateHeight(cm));

    if (!cm.options.lineWrapping) {
      doc.iter(checkWidthStart, from.line + change.text.length, function(line) {
        var len = lineLength(line);
        if (len > display.maxLineLength) {
          display.maxLine = line;
          display.maxLineLength = len;
          display.maxLineChanged = true;
          recomputeMaxLength = false;
        }
      });
      if (recomputeMaxLength) cm.curOp.updateMaxLine = true;
    }

    // Adjust frontier, schedule worker
    doc.frontier = Math.min(doc.frontier, from.line);
    startWorker(cm, 400);

    var lendiff = change.text.length - (to.line - from.line) - 1;
    // Remember that these lines changed, for updating the display
    if (change.full)
      regChange(cm);
    else if (from.line == to.line && change.text.length == 1 && !isWholeLineUpdate(cm.doc, change))
      regLineChange(cm, from.line, "text");
    else
      regChange(cm, from.line, to.line + 1, lendiff);

    var changesHandler = hasHandler(cm, "changes"), changeHandler = hasHandler(cm, "change");
    if (changeHandler || changesHandler) {
      var obj = {
        from: from, to: to,
        text: change.text,
        removed: change.removed,
        origin: change.origin
      };
      if (changeHandler) signalLater(cm, "change", cm, obj);
      if (changesHandler) (cm.curOp.changeObjs || (cm.curOp.changeObjs = [])).push(obj);
    }
    cm.display.selForContextMenu = null;
  }

  function replaceRange(doc, code, from, to, origin) {
    if (!to) to = from;
    if (cmp(to, from) < 0) { var tmp = to; to = from; from = tmp; }
    if (typeof code == "string") code = doc.splitLines(code);
    makeChange(doc, {from: from, to: to, text: code, origin: origin});
  }

  // SCROLLING THINGS INTO VIEW

  // If an editor sits on the top or bottom of the window, partially
  // scrolled out of view, this ensures that the cursor is visible.
  function maybeScrollWindow(cm, coords) {
    if (signalDOMEvent(cm, "scrollCursorIntoView")) return;

    var display = cm.display, box = display.sizer.getBoundingClientRect(), doScroll = null;
    if (coords.top + box.top < 0) doScroll = true;
    else if (coords.bottom + box.top > (window.innerHeight || document.documentElement.clientHeight)) doScroll = false;
    if (doScroll != null && !phantom) {
      var scrollNode = elt("div", "\u200b", null, "position: absolute; top: " +
                           (coords.top - display.viewOffset - paddingTop(cm.display)) + "px; height: " +
                           (coords.bottom - coords.top + scrollGap(cm) + display.barHeight) + "px; left: " +
                           coords.left + "px; width: 2px;");
      cm.display.lineSpace.appendChild(scrollNode);
      scrollNode.scrollIntoView(doScroll);
      cm.display.lineSpace.removeChild(scrollNode);
    }
  }

  // Scroll a given position into view (immediately), verifying that
  // it actually became visible (as line heights are accurately
  // measured, the position of something may 'drift' during drawing).
  function scrollPosIntoView(cm, pos, end, margin) {
    if (margin == null) margin = 0;
    for (var limit = 0; limit < 5; limit++) {
      var changed = false, coords = cursorCoords(cm, pos);
      var endCoords = !end || end == pos ? coords : cursorCoords(cm, end);
      var scrollPos = calculateScrollPos(cm, Math.min(coords.left, endCoords.left),
                                         Math.min(coords.top, endCoords.top) - margin,
                                         Math.max(coords.left, endCoords.left),
                                         Math.max(coords.bottom, endCoords.bottom) + margin);
      var startTop = cm.doc.scrollTop, startLeft = cm.doc.scrollLeft;
      if (scrollPos.scrollTop != null) {
        setScrollTop(cm, scrollPos.scrollTop);
        if (Math.abs(cm.doc.scrollTop - startTop) > 1) changed = true;
      }
      if (scrollPos.scrollLeft != null) {
        setScrollLeft(cm, scrollPos.scrollLeft);
        if (Math.abs(cm.doc.scrollLeft - startLeft) > 1) changed = true;
      }
      if (!changed) break;
    }
    return coords;
  }

  // Scroll a given set of coordinates into view (immediately).
  function scrollIntoView(cm, x1, y1, x2, y2) {
    var scrollPos = calculateScrollPos(cm, x1, y1, x2, y2);
    if (scrollPos.scrollTop != null) setScrollTop(cm, scrollPos.scrollTop);
    if (scrollPos.scrollLeft != null) setScrollLeft(cm, scrollPos.scrollLeft);
  }

  // Calculate a new scroll position needed to scroll the given
  // rectangle into view. Returns an object with scrollTop and
  // scrollLeft properties. When these are undefined, the
  // vertical/horizontal position does not need to be adjusted.
  function calculateScrollPos(cm, x1, y1, x2, y2) {
    var display = cm.display, snapMargin = textHeight(cm.display);
    if (y1 < 0) y1 = 0;
    var screentop = cm.curOp && cm.curOp.scrollTop != null ? cm.curOp.scrollTop : display.scroller.scrollTop;
    var screen = displayHeight(cm), result = {};
    if (y2 - y1 > screen) y2 = y1 + screen;
    var docBottom = cm.doc.height + paddingVert(display);
    var atTop = y1 < snapMargin, atBottom = y2 > docBottom - snapMargin;
    if (y1 < screentop) {
      result.scrollTop = atTop ? 0 : y1;
    } else if (y2 > screentop + screen) {
      var newTop = Math.min(y1, (atBottom ? docBottom : y2) - screen);
      if (newTop != screentop) result.scrollTop = newTop;
    }

    var screenleft = cm.curOp && cm.curOp.scrollLeft != null ? cm.curOp.scrollLeft : display.scroller.scrollLeft;
    var screenw = displayWidth(cm) - (cm.options.fixedGutter ? display.gutters.offsetWidth : 0);
    var tooWide = x2 - x1 > screenw;
    if (tooWide) x2 = x1 + screenw;
    if (x1 < 10)
      result.scrollLeft = 0;
    else if (x1 < screenleft)
      result.scrollLeft = Math.max(0, x1 - (tooWide ? 0 : 10));
    else if (x2 > screenw + screenleft - 3)
      result.scrollLeft = x2 + (tooWide ? 0 : 10) - screenw;
    return result;
  }

  // Store a relative adjustment to the scroll position in the current
  // operation (to be applied when the operation finishes).
  function addToScrollPos(cm, left, top) {
    if (left != null || top != null) resolveScrollToPos(cm);
    if (left != null)
      cm.curOp.scrollLeft = (cm.curOp.scrollLeft == null ? cm.doc.scrollLeft : cm.curOp.scrollLeft) + left;
    if (top != null)
      cm.curOp.scrollTop = (cm.curOp.scrollTop == null ? cm.doc.scrollTop : cm.curOp.scrollTop) + top;
  }

  // Make sure that at the end of the operation the current cursor is
  // shown.
  function ensureCursorVisible(cm) {
    resolveScrollToPos(cm);
    var cur = cm.getCursor(), from = cur, to = cur;
    if (!cm.options.lineWrapping) {
      from = cur.ch ? Pos(cur.line, cur.ch - 1) : cur;
      to = Pos(cur.line, cur.ch + 1);
    }
    cm.curOp.scrollToPos = {from: from, to: to, margin: cm.options.cursorScrollMargin, isCursor: true};
  }

  // When an operation has its scrollToPos property set, and another
  // scroll action is applied before the end of the operation, this
  // 'simulates' scrolling that position into view in a cheap way, so
  // that the effect of intermediate scroll commands is not ignored.
  function resolveScrollToPos(cm) {
    var range = cm.curOp.scrollToPos;
    if (range) {
      cm.curOp.scrollToPos = null;
      var from = estimateCoords(cm, range.from), to = estimateCoords(cm, range.to);
      var sPos = calculateScrollPos(cm, Math.min(from.left, to.left),
                                    Math.min(from.top, to.top) - range.margin,
                                    Math.max(from.right, to.right),
                                    Math.max(from.bottom, to.bottom) + range.margin);
      cm.scrollTo(sPos.scrollLeft, sPos.scrollTop);
    }
  }

  // API UTILITIES

  // Indent the given line. The how parameter can be "smart",
  // "add"/null, "subtract", or "prev". When aggressive is false
  // (typically set to true for forced single-line indents), empty
  // lines are not indented, and places where the mode returns Pass
  // are left alone.
  function indentLine(cm, n, how, aggressive) {
    var doc = cm.doc, state;
    if (how == null) how = "add";
    if (how == "smart") {
      // Fall back to "prev" when the mode doesn't have an indentation
      // method.
      if (!doc.mode.indent) how = "prev";
      else state = getStateBefore(cm, n);
    }

    var tabSize = cm.options.tabSize;
    var line = getLine(doc, n), curSpace = countColumn(line.text, null, tabSize);
    if (line.stateAfter) line.stateAfter = null;
    var curSpaceString = line.text.match(/^\s*/)[0], indentation;
    if (!aggressive && !/\S/.test(line.text)) {
      indentation = 0;
      how = "not";
    } else if (how == "smart") {
      indentation = doc.mode.indent(state, line.text.slice(curSpaceString.length), line.text);
      if (indentation == Pass || indentation > 150) {
        if (!aggressive) return;
        how = "prev";
      }
    }
    if (how == "prev") {
      if (n > doc.first) indentation = countColumn(getLine(doc, n-1).text, null, tabSize);
      else indentation = 0;
    } else if (how == "add") {
      indentation = curSpace + cm.options.indentUnit;
    } else if (how == "subtract") {
      indentation = curSpace - cm.options.indentUnit;
    } else if (typeof how == "number") {
      indentation = curSpace + how;
    }
    indentation = Math.max(0, indentation);

    var indentString = "", pos = 0;
    if (cm.options.indentWithTabs)
      for (var i = Math.floor(indentation / tabSize); i; --i) {pos += tabSize; indentString += "\t";}
    if (pos < indentation) indentString += spaceStr(indentation - pos);

    if (indentString != curSpaceString) {
      replaceRange(doc, indentString, Pos(n, 0), Pos(n, curSpaceString.length), "+input");
      line.stateAfter = null;
      return true;
    } else {
      // Ensure that, if the cursor was in the whitespace at the start
      // of the line, it is moved to the end of that space.
      for (var i = 0; i < doc.sel.ranges.length; i++) {
        var range = doc.sel.ranges[i];
        if (range.head.line == n && range.head.ch < curSpaceString.length) {
          var pos = Pos(n, curSpaceString.length);
          replaceOneSelection(doc, i, new Range(pos, pos));
          break;
        }
      }
    }
  }

  // Utility for applying a change to a line by handle or number,
  // returning the number and optionally registering the line as
  // changed.
  function changeLine(doc, handle, changeType, op) {
    var no = handle, line = handle;
    if (typeof handle == "number") line = getLine(doc, clipLine(doc, handle));
    else no = lineNo(handle);
    if (no == null) return null;
    if (op(line, no) && doc.cm) regLineChange(doc.cm, no, changeType);
    return line;
  }

  // Helper for deleting text near the selection(s), used to implement
  // backspace, delete, and similar functionality.
  function deleteNearSelection(cm, compute) {
    var ranges = cm.doc.sel.ranges, kill = [];
    // Build up a set of ranges to kill first, merging overlapping
    // ranges.
    for (var i = 0; i < ranges.length; i++) {
      var toKill = compute(ranges[i]);
      while (kill.length && cmp(toKill.from, lst(kill).to) <= 0) {
        var replaced = kill.pop();
        if (cmp(replaced.from, toKill.from) < 0) {
          toKill.from = replaced.from;
          break;
        }
      }
      kill.push(toKill);
    }
    // Next, remove those actual ranges.
    runInOp(cm, function() {
      for (var i = kill.length - 1; i >= 0; i--)
        replaceRange(cm.doc, "", kill[i].from, kill[i].to, "+delete");
      ensureCursorVisible(cm);
    });
  }

  // Used for horizontal relative motion. Dir is -1 or 1 (left or
  // right), unit can be "char", "column" (like char, but doesn't
  // cross line boundaries), "word" (across next word), or "group" (to
  // the start of next group of word or non-word-non-whitespace
  // chars). The visually param controls whether, in right-to-left
  // text, direction 1 means to move towards the next index in the
  // string, or towards the character to the right of the current
  // position. The resulting position will have a hitSide=true
  // property if it reached the end of the document.
  function findPosH(doc, pos, dir, unit, visually) {
    var line = pos.line, ch = pos.ch, origDir = dir;
    var lineObj = getLine(doc, line);
    function findNextLine() {
      var l = line + dir;
      if (l < doc.first || l >= doc.first + doc.size) return false
      line = l;
      return lineObj = getLine(doc, l);
    }
    function moveOnce(boundToLine) {
      var next = (visually ? moveVisually : moveLogically)(lineObj, ch, dir, true);
      if (next == null) {
        if (!boundToLine && findNextLine()) {
          if (visually) ch = (dir < 0 ? lineRight : lineLeft)(lineObj);
          else ch = dir < 0 ? lineObj.text.length : 0;
        } else return false
      } else ch = next;
      return true;
    }

    if (unit == "char") {
      moveOnce()
    } else if (unit == "column") {
      moveOnce(true)
    } else if (unit == "word" || unit == "group") {
      var sawType = null, group = unit == "group";
      var helper = doc.cm && doc.cm.getHelper(pos, "wordChars");
      for (var first = true;; first = false) {
        if (dir < 0 && !moveOnce(!first)) break;
        var cur = lineObj.text.charAt(ch) || "\n";
        var type = isWordChar(cur, helper) ? "w"
          : group && cur == "\n" ? "n"
          : !group || /\s/.test(cur) ? null
          : "p";
        if (group && !first && !type) type = "s";
        if (sawType && sawType != type) {
          if (dir < 0) {dir = 1; moveOnce();}
          break;
        }

        if (type) sawType = type;
        if (dir > 0 && !moveOnce(!first)) break;
      }
    }
    var result = skipAtomic(doc, Pos(line, ch), pos, origDir, true);
    if (!cmp(pos, result)) result.hitSide = true;
    return result;
  }

  // For relative vertical movement. Dir may be -1 or 1. Unit can be
  // "page" or "line". The resulting position will have a hitSide=true
  // property if it reached the end of the document.
  function findPosV(cm, pos, dir, unit) {
    var doc = cm.doc, x = pos.left, y;
    if (unit == "page") {
      var pageSize = Math.min(cm.display.wrapper.clientHeight, window.innerHeight || document.documentElement.clientHeight);
      y = pos.top + dir * (pageSize - (dir < 0 ? 1.5 : .5) * textHeight(cm.display));
    } else if (unit == "line") {
      y = dir > 0 ? pos.bottom + 3 : pos.top - 3;
    }
    for (;;) {
      var target = coordsChar(cm, x, y);
      if (!target.outside) break;
      if (dir < 0 ? y <= 0 : y >= doc.height) { target.hitSide = true; break; }
      y += dir * 5;
    }
    return target;
  }

  // EDITOR METHODS

  // The publicly visible API. Note that methodOp(f) means
  // 'wrap f in an operation, performed on its `this` parameter'.

  // This is not the complete set of editor methods. Most of the
  // methods defined on the Doc type are also injected into
  // CodeMirror.prototype, for backwards compatibility and
  // convenience.

  CodeMirror.prototype = {
    constructor: CodeMirror,
    focus: function(){window.focus(); this.display.input.focus();},

    setOption: function(option, value) {
      var options = this.options, old = options[option];
      if (options[option] == value && option != "mode") return;
      options[option] = value;
      if (optionHandlers.hasOwnProperty(option))
        operation(this, optionHandlers[option])(this, value, old);
    },

    getOption: function(option) {return this.options[option];},
    getDoc: function() {return this.doc;},

    addKeyMap: function(map, bottom) {
      this.state.keyMaps[bottom ? "push" : "unshift"](getKeyMap(map));
    },
    removeKeyMap: function(map) {
      var maps = this.state.keyMaps;
      for (var i = 0; i < maps.length; ++i)
        if (maps[i] == map || maps[i].name == map) {
          maps.splice(i, 1);
          return true;
        }
    },

    addOverlay: methodOp(function(spec, options) {
      var mode = spec.token ? spec : CodeMirror.getMode(this.options, spec);
      if (mode.startState) throw new Error("Overlays may not be stateful.");
      this.state.overlays.push({mode: mode, modeSpec: spec, opaque: options && options.opaque});
      this.state.modeGen++;
      regChange(this);
    }),
    removeOverlay: methodOp(function(spec) {
      var overlays = this.state.overlays;
      for (var i = 0; i < overlays.length; ++i) {
        var cur = overlays[i].modeSpec;
        if (cur == spec || typeof spec == "string" && cur.name == spec) {
          overlays.splice(i, 1);
          this.state.modeGen++;
          regChange(this);
          return;
        }
      }
    }),

    indentLine: methodOp(function(n, dir, aggressive) {
      if (typeof dir != "string" && typeof dir != "number") {
        if (dir == null) dir = this.options.smartIndent ? "smart" : "prev";
        else dir = dir ? "add" : "subtract";
      }
      if (isLine(this.doc, n)) indentLine(this, n, dir, aggressive);
    }),
    indentSelection: methodOp(function(how) {
      var ranges = this.doc.sel.ranges, end = -1;
      for (var i = 0; i < ranges.length; i++) {
        var range = ranges[i];
        if (!range.empty()) {
          var from = range.from(), to = range.to();
          var start = Math.max(end, from.line);
          end = Math.min(this.lastLine(), to.line - (to.ch ? 0 : 1)) + 1;
          for (var j = start; j < end; ++j)
            indentLine(this, j, how);
          var newRanges = this.doc.sel.ranges;
          if (from.ch == 0 && ranges.length == newRanges.length && newRanges[i].from().ch > 0)
            replaceOneSelection(this.doc, i, new Range(from, newRanges[i].to()), sel_dontScroll);
        } else if (range.head.line > end) {
          indentLine(this, range.head.line, how, true);
          end = range.head.line;
          if (i == this.doc.sel.primIndex) ensureCursorVisible(this);
        }
      }
    }),

    // Fetch the parser token for a given character. Useful for hacks
    // that want to inspect the mode state (say, for completion).
    getTokenAt: function(pos, precise) {
      return takeToken(this, pos, precise);
    },

    getLineTokens: function(line, precise) {
      return takeToken(this, Pos(line), precise, true);
    },

    getTokenTypeAt: function(pos) {
      pos = clipPos(this.doc, pos);
      var styles = getLineStyles(this, getLine(this.doc, pos.line));
      var before = 0, after = (styles.length - 1) / 2, ch = pos.ch;
      var type;
      if (ch == 0) type = styles[2];
      else for (;;) {
        var mid = (before + after) >> 1;
        if ((mid ? styles[mid * 2 - 1] : 0) >= ch) after = mid;
        else if (styles[mid * 2 + 1] < ch) before = mid + 1;
        else { type = styles[mid * 2 + 2]; break; }
      }
      var cut = type ? type.indexOf("cm-overlay ") : -1;
      return cut < 0 ? type : cut == 0 ? null : type.slice(0, cut - 1);
    },

    getModeAt: function(pos) {
      var mode = this.doc.mode;
      if (!mode.innerMode) return mode;
      return CodeMirror.innerMode(mode, this.getTokenAt(pos).state).mode;
    },

    getHelper: function(pos, type) {
      return this.getHelpers(pos, type)[0];
    },

    getHelpers: function(pos, type) {
      var found = [];
      if (!helpers.hasOwnProperty(type)) return found;
      var help = helpers[type], mode = this.getModeAt(pos);
      if (typeof mode[type] == "string") {
        if (help[mode[type]]) found.push(help[mode[type]]);
      } else if (mode[type]) {
        for (var i = 0; i < mode[type].length; i++) {
          var val = help[mode[type][i]];
          if (val) found.push(val);
        }
      } else if (mode.helperType && help[mode.helperType]) {
        found.push(help[mode.helperType]);
      } else if (help[mode.name]) {
        found.push(help[mode.name]);
      }
      for (var i = 0; i < help._global.length; i++) {
        var cur = help._global[i];
        if (cur.pred(mode, this) && indexOf(found, cur.val) == -1)
          found.push(cur.val);
      }
      return found;
    },

    getStateAfter: function(line, precise) {
      var doc = this.doc;
      line = clipLine(doc, line == null ? doc.first + doc.size - 1: line);
      return getStateBefore(this, line + 1, precise);
    },

    cursorCoords: function(start, mode) {
      var pos, range = this.doc.sel.primary();
      if (start == null) pos = range.head;
      else if (typeof start == "object") pos = clipPos(this.doc, start);
      else pos = start ? range.from() : range.to();
      return cursorCoords(this, pos, mode || "page");
    },

    charCoords: function(pos, mode) {
      return charCoords(this, clipPos(this.doc, pos), mode || "page");
    },

    coordsChar: function(coords, mode) {
      coords = fromCoordSystem(this, coords, mode || "page");
      return coordsChar(this, coords.left, coords.top);
    },

    lineAtHeight: function(height, mode) {
      height = fromCoordSystem(this, {top: height, left: 0}, mode || "page").top;
      return lineAtHeight(this.doc, height + this.display.viewOffset);
    },
    heightAtLine: function(line, mode) {
      var end = false, lineObj;
      if (typeof line == "number") {
        var last = this.doc.first + this.doc.size - 1;
        if (line < this.doc.first) line = this.doc.first;
        else if (line > last) { line = last; end = true; }
        lineObj = getLine(this.doc, line);
      } else {
        lineObj = line;
      }
      return intoCoordSystem(this, lineObj, {top: 0, left: 0}, mode || "page").top +
        (end ? this.doc.height - heightAtLine(lineObj) : 0);
    },

    defaultTextHeight: function() { return textHeight(this.display); },
    defaultCharWidth: function() { return charWidth(this.display); },

    setGutterMarker: methodOp(function(line, gutterID, value) {
      return changeLine(this.doc, line, "gutter", function(line) {
        var markers = line.gutterMarkers || (line.gutterMarkers = {});
        markers[gutterID] = value;
        if (!value && isEmpty(markers)) line.gutterMarkers = null;
        return true;
      });
    }),

    clearGutter: methodOp(function(gutterID) {
      var cm = this, doc = cm.doc, i = doc.first;
      doc.iter(function(line) {
        if (line.gutterMarkers && line.gutterMarkers[gutterID]) {
          line.gutterMarkers[gutterID] = null;
          regLineChange(cm, i, "gutter");
          if (isEmpty(line.gutterMarkers)) line.gutterMarkers = null;
        }
        ++i;
      });
    }),

    lineInfo: function(line) {
      if (typeof line == "number") {
        if (!isLine(this.doc, line)) return null;
        var n = line;
        line = getLine(this.doc, line);
        if (!line) return null;
      } else {
        var n = lineNo(line);
        if (n == null) return null;
      }
      return {line: n, handle: line, text: line.text, gutterMarkers: line.gutterMarkers,
              textClass: line.textClass, bgClass: line.bgClass, wrapClass: line.wrapClass,
              widgets: line.widgets};
    },

    getViewport: function() { return {from: this.display.viewFrom, to: this.display.viewTo};},

    addWidget: function(pos, node, scroll, vert, horiz) {
      var display = this.display;
      pos = cursorCoords(this, clipPos(this.doc, pos));
      var top = pos.bottom, left = pos.left;
      node.style.position = "absolute";
      node.setAttribute("cm-ignore-events", "true");
      this.display.input.setUneditable(node);
      display.sizer.appendChild(node);
      if (vert == "over") {
        top = pos.top;
      } else if (vert == "above" || vert == "near") {
        var vspace = Math.max(display.wrapper.clientHeight, this.doc.height),
        hspace = Math.max(display.sizer.clientWidth, display.lineSpace.clientWidth);
        // Default to positioning above (if specified and possible); otherwise default to positioning below
        if ((vert == 'above' || pos.bottom + node.offsetHeight > vspace) && pos.top > node.offsetHeight)
          top = pos.top - node.offsetHeight;
        else if (pos.bottom + node.offsetHeight <= vspace)
          top = pos.bottom;
        if (left + node.offsetWidth > hspace)
          left = hspace - node.offsetWidth;
      }
      node.style.top = top + "px";
      node.style.left = node.style.right = "";
      if (horiz == "right") {
        left = display.sizer.clientWidth - node.offsetWidth;
        node.style.right = "0px";
      } else {
        if (horiz == "left") left = 0;
        else if (horiz == "middle") left = (display.sizer.clientWidth - node.offsetWidth) / 2;
        node.style.left = left + "px";
      }
      if (scroll)
        scrollIntoView(this, left, top, left + node.offsetWidth, top + node.offsetHeight);
    },

    triggerOnKeyDown: methodOp(onKeyDown),
    triggerOnKeyPress: methodOp(onKeyPress),
    triggerOnKeyUp: onKeyUp,

    execCommand: function(cmd) {
      if (commands.hasOwnProperty(cmd))
        return commands[cmd].call(null, this);
    },

    triggerElectric: methodOp(function(text) { triggerElectric(this, text); }),

    findPosH: function(from, amount, unit, visually) {
      var dir = 1;
      if (amount < 0) { dir = -1; amount = -amount; }
      for (var i = 0, cur = clipPos(this.doc, from); i < amount; ++i) {
        cur = findPosH(this.doc, cur, dir, unit, visually);
        if (cur.hitSide) break;
      }
      return cur;
    },

    moveH: methodOp(function(dir, unit) {
      var cm = this;
      cm.extendSelectionsBy(function(range) {
        if (cm.display.shift || cm.doc.extend || range.empty())
          return findPosH(cm.doc, range.head, dir, unit, cm.options.rtlMoveVisually);
        else
          return dir < 0 ? range.from() : range.to();
      }, sel_move);
    }),

    deleteH: methodOp(function(dir, unit) {
      var sel = this.doc.sel, doc = this.doc;
      if (sel.somethingSelected())
        doc.replaceSelection("", null, "+delete");
      else
        deleteNearSelection(this, function(range) {
          var other = findPosH(doc, range.head, dir, unit, false);
          return dir < 0 ? {from: other, to: range.head} : {from: range.head, to: other};
        });
    }),

    findPosV: function(from, amount, unit, goalColumn) {
      var dir = 1, x = goalColumn;
      if (amount < 0) { dir = -1; amount = -amount; }
      for (var i = 0, cur = clipPos(this.doc, from); i < amount; ++i) {
        var coords = cursorCoords(this, cur, "div");
        if (x == null) x = coords.left;
        else coords.left = x;
        cur = findPosV(this, coords, dir, unit);
        if (cur.hitSide) break;
      }
      return cur;
    },

    moveV: methodOp(function(dir, unit) {
      var cm = this, doc = this.doc, goals = [];
      var collapse = !cm.display.shift && !doc.extend && doc.sel.somethingSelected();
      doc.extendSelectionsBy(function(range) {
        if (collapse)
          return dir < 0 ? range.from() : range.to();
        var headPos = cursorCoords(cm, range.head, "div");
        if (range.goalColumn != null) headPos.left = range.goalColumn;
        goals.push(headPos.left);
        var pos = findPosV(cm, headPos, dir, unit);
        if (unit == "page" && range == doc.sel.primary())
          addToScrollPos(cm, null, charCoords(cm, pos, "div").top - headPos.top);
        return pos;
      }, sel_move);
      if (goals.length) for (var i = 0; i < doc.sel.ranges.length; i++)
        doc.sel.ranges[i].goalColumn = goals[i];
    }),

    // Find the word at the given position (as returned by coordsChar).
    findWordAt: function(pos) {
      var doc = this.doc, line = getLine(doc, pos.line).text;
      var start = pos.ch, end = pos.ch;
      if (line) {
        var helper = this.getHelper(pos, "wordChars");
        if ((pos.xRel < 0 || end == line.length) && start) --start; else ++end;
        var startChar = line.charAt(start);
        var check = isWordChar(startChar, helper)
          ? function(ch) { return isWordChar(ch, helper); }
          : /\s/.test(startChar) ? function(ch) {return /\s/.test(ch);}
          : function(ch) {return !/\s/.test(ch) && !isWordChar(ch);};
        while (start > 0 && check(line.charAt(start - 1))) --start;
        while (end < line.length && check(line.charAt(end))) ++end;
      }
      return new Range(Pos(pos.line, start), Pos(pos.line, end));
    },

    toggleOverwrite: function(value) {
      if (value != null && value == this.state.overwrite) return;
      if (this.state.overwrite = !this.state.overwrite)
        addClass(this.display.cursorDiv, "CodeMirror-overwrite");
      else
        rmClass(this.display.cursorDiv, "CodeMirror-overwrite");

      signal(this, "overwriteToggle", this, this.state.overwrite);
    },
    hasFocus: function() { return this.display.input.getField() == activeElt(); },
    isReadOnly: function() { return !!(this.options.readOnly || this.doc.cantEdit); },

    scrollTo: methodOp(function(x, y) {
      if (x != null || y != null) resolveScrollToPos(this);
      if (x != null) this.curOp.scrollLeft = x;
      if (y != null) this.curOp.scrollTop = y;
    }),
    getScrollInfo: function() {
      var scroller = this.display.scroller;
      return {left: scroller.scrollLeft, top: scroller.scrollTop,
              height: scroller.scrollHeight - scrollGap(this) - this.display.barHeight,
              width: scroller.scrollWidth - scrollGap(this) - this.display.barWidth,
              clientHeight: displayHeight(this), clientWidth: displayWidth(this)};
    },

    scrollIntoView: methodOp(function(range, margin) {
      if (range == null) {
        range = {from: this.doc.sel.primary().head, to: null};
        if (margin == null) margin = this.options.cursorScrollMargin;
      } else if (typeof range == "number") {
        range = {from: Pos(range, 0), to: null};
      } else if (range.from == null) {
        range = {from: range, to: null};
      }
      if (!range.to) range.to = range.from;
      range.margin = margin || 0;

      if (range.from.line != null) {
        resolveScrollToPos(this);
        this.curOp.scrollToPos = range;
      } else {
        var sPos = calculateScrollPos(this, Math.min(range.from.left, range.to.left),
                                      Math.min(range.from.top, range.to.top) - range.margin,
                                      Math.max(range.from.right, range.to.right),
                                      Math.max(range.from.bottom, range.to.bottom) + range.margin);
        this.scrollTo(sPos.scrollLeft, sPos.scrollTop);
      }
    }),

    setSize: methodOp(function(width, height) {
      var cm = this;
      function interpret(val) {
        return typeof val == "number" || /^\d+$/.test(String(val)) ? val + "px" : val;
      }
      if (width != null) cm.display.wrapper.style.width = interpret(width);
      if (height != null) cm.display.wrapper.style.height = interpret(height);
      if (cm.options.lineWrapping) clearLineMeasurementCache(this);
      var lineNo = cm.display.viewFrom;
      cm.doc.iter(lineNo, cm.display.viewTo, function(line) {
        if (line.widgets) for (var i = 0; i < line.widgets.length; i++)
          if (line.widgets[i].noHScroll) { regLineChange(cm, lineNo, "widget"); break; }
        ++lineNo;
      });
      cm.curOp.forceUpdate = true;
      signal(cm, "refresh", this);
    }),

    operation: function(f){return runInOp(this, f);},

    refresh: methodOp(function() {
      var oldHeight = this.display.cachedTextHeight;
      regChange(this);
      this.curOp.forceUpdate = true;
      clearCaches(this);
      this.scrollTo(this.doc.scrollLeft, this.doc.scrollTop);
      updateGutterSpace(this);
      if (oldHeight == null || Math.abs(oldHeight - textHeight(this.display)) > .5)
        estimateLineHeights(this);
      signal(this, "refresh", this);
    }),

    swapDoc: methodOp(function(doc) {
      var old = this.doc;
      old.cm = null;
      attachDoc(this, doc);
      clearCaches(this);
      this.display.input.reset();
      this.scrollTo(doc.scrollLeft, doc.scrollTop);
      this.curOp.forceScroll = true;
      signalLater(this, "swapDoc", this, old);
      return old;
    }),

    getInputField: function(){return this.display.input.getField();},
    getWrapperElement: function(){return this.display.wrapper;},
    getScrollerElement: function(){return this.display.scroller;},
    getGutterElement: function(){return this.display.gutters;}
  };
  eventMixin(CodeMirror);

  // OPTION DEFAULTS

  // The default configuration options.
  var defaults = CodeMirror.defaults = {};
  // Functions to run when options are changed.
  var optionHandlers = CodeMirror.optionHandlers = {};

  function option(name, deflt, handle, notOnInit) {
    CodeMirror.defaults[name] = deflt;
    if (handle) optionHandlers[name] =
      notOnInit ? function(cm, val, old) {if (old != Init) handle(cm, val, old);} : handle;
  }

  // Passed to option handlers when there is no old value.
  var Init = CodeMirror.Init = {toString: function(){return "CodeMirror.Init";}};

  // These two are, on init, called from the constructor because they
  // have to be initialized before the editor can start at all.
  option("value", "", function(cm, val) {
    cm.setValue(val);
  }, true);
  option("mode", null, function(cm, val) {
    cm.doc.modeOption = val;
    loadMode(cm);
  }, true);

  option("indentUnit", 2, loadMode, true);
  option("indentWithTabs", false);
  option("smartIndent", true);
  option("tabSize", 4, function(cm) {
    resetModeState(cm);
    clearCaches(cm);
    regChange(cm);
  }, true);
  option("lineSeparator", null, function(cm, val) {
    cm.doc.lineSep = val;
    if (!val) return;
    var newBreaks = [], lineNo = cm.doc.first;
    cm.doc.iter(function(line) {
      for (var pos = 0;;) {
        var found = line.text.indexOf(val, pos);
        if (found == -1) break;
        pos = found + val.length;
        newBreaks.push(Pos(lineNo, found));
      }
      lineNo++;
    });
    for (var i = newBreaks.length - 1; i >= 0; i--)
      replaceRange(cm.doc, val, newBreaks[i], Pos(newBreaks[i].line, newBreaks[i].ch + val.length))
  });
  option("specialChars", /[\u0000-\u001f\u007f\u00ad\u200b-\u200f\u2028\u2029\ufeff]/g, function(cm, val, old) {
    cm.state.specialChars = new RegExp(val.source + (val.test("\t") ? "" : "|\t"), "g");
    if (old != CodeMirror.Init) cm.refresh();
  });
  option("specialCharPlaceholder", defaultSpecialCharPlaceholder, function(cm) {cm.refresh();}, true);
  option("electricChars", true);
  option("inputStyle", mobile ? "contenteditable" : "textarea", function() {
    throw new Error("inputStyle can not (yet) be changed in a running editor"); // FIXME
  }, true);
  option("rtlMoveVisually", !windows);
  option("wholeLineUpdateBefore", true);

  option("theme", "default", function(cm) {
    themeChanged(cm);
    guttersChanged(cm);
  }, true);
  option("keyMap", "default", function(cm, val, old) {
    var next = getKeyMap(val);
    var prev = old != CodeMirror.Init && getKeyMap(old);
    if (prev && prev.detach) prev.detach(cm, next);
    if (next.attach) next.attach(cm, prev || null);
  });
  option("extraKeys", null);

  option("lineWrapping", false, wrappingChanged, true);
  option("gutters", [], function(cm) {
    setGuttersForLineNumbers(cm.options);
    guttersChanged(cm);
  }, true);
  option("fixedGutter", true, function(cm, val) {
    cm.display.gutters.style.left = val ? compensateForHScroll(cm.display) + "px" : "0";
    cm.refresh();
  }, true);
  option("coverGutterNextToScrollbar", false, function(cm) {updateScrollbars(cm);}, true);
  option("scrollbarStyle", "native", function(cm) {
    initScrollbars(cm);
    updateScrollbars(cm);
    cm.display.scrollbars.setScrollTop(cm.doc.scrollTop);
    cm.display.scrollbars.setScrollLeft(cm.doc.scrollLeft);
  }, true);
  option("lineNumbers", false, function(cm) {
    setGuttersForLineNumbers(cm.options);
    guttersChanged(cm);
  }, true);
  option("firstLineNumber", 1, guttersChanged, true);
  option("lineNumberFormatter", function(integer) {return integer;}, guttersChanged, true);
  option("showCursorWhenSelecting", false, updateSelection, true);

  option("resetSelectionOnContextMenu", true);
  option("lineWiseCopyCut", true);

  option("readOnly", false, function(cm, val) {
    if (val == "nocursor") {
      onBlur(cm);
      cm.display.input.blur();
      cm.display.disabled = true;
    } else {
      cm.display.disabled = false;
    }
    cm.display.input.readOnlyChanged(val)
  });
  option("disableInput", false, function(cm, val) {if (!val) cm.display.input.reset();}, true);
  option("dragDrop", true, dragDropChanged);
  option("allowDropFileTypes", null);

  option("cursorBlinkRate", 530);
  option("cursorScrollMargin", 0);
  option("cursorHeight", 1, updateSelection, true);
  option("singleCursorHeightPerLine", true, updateSelection, true);
  option("workTime", 100);
  option("workDelay", 100);
  option("flattenSpans", true, resetModeState, true);
  option("addModeClass", false, resetModeState, true);
  option("pollInterval", 100);
  option("undoDepth", 200, function(cm, val){cm.doc.history.undoDepth = val;});
  option("historyEventDelay", 1250);
  option("viewportMargin", 10, function(cm){cm.refresh();}, true);
  option("maxHighlightLength", 10000, resetModeState, true);
  option("moveInputWithCursor", true, function(cm, val) {
    if (!val) cm.display.input.resetPosition();
  });

  option("tabindex", null, function(cm, val) {
    cm.display.input.getField().tabIndex = val || "";
  });
  option("autofocus", null);

  // MODE DEFINITION AND QUERYING

  // Known modes, by name and by MIME
  var modes = CodeMirror.modes = {}, mimeModes = CodeMirror.mimeModes = {};

  // Extra arguments are stored as the mode's dependencies, which is
  // used by (legacy) mechanisms like loadmode.js to automatically
  // load a mode. (Preferred mechanism is the require/define calls.)
  CodeMirror.defineMode = function(name, mode) {
    if (!CodeMirror.defaults.mode && name != "null") CodeMirror.defaults.mode = name;
    if (arguments.length > 2)
      mode.dependencies = Array.prototype.slice.call(arguments, 2);
    modes[name] = mode;
  };

  CodeMirror.defineMIME = function(mime, spec) {
    mimeModes[mime] = spec;
  };

  // Given a MIME type, a {name, ...options} config object, or a name
  // string, return a mode config object.
  CodeMirror.resolveMode = function(spec) {
    if (typeof spec == "string" && mimeModes.hasOwnProperty(spec)) {
      spec = mimeModes[spec];
    } else if (spec && typeof spec.name == "string" && mimeModes.hasOwnProperty(spec.name)) {
      var found = mimeModes[spec.name];
      if (typeof found == "string") found = {name: found};
      spec = createObj(found, spec);
      spec.name = found.name;
    } else if (typeof spec == "string" && /^[\w\-]+\/[\w\-]+\+xml$/.test(spec)) {
      return CodeMirror.resolveMode("application/xml");
    }
    if (typeof spec == "string") return {name: spec};
    else return spec || {name: "null"};
  };

  // Given a mode spec (anything that resolveMode accepts), find and
  // initialize an actual mode object.
  CodeMirror.getMode = function(options, spec) {
    var spec = CodeMirror.resolveMode(spec);
    var mfactory = modes[spec.name];
    if (!mfactory) return CodeMirror.getMode(options, "text/plain");
    var modeObj = mfactory(options, spec);
    if (modeExtensions.hasOwnProperty(spec.name)) {
      var exts = modeExtensions[spec.name];
      for (var prop in exts) {
        if (!exts.hasOwnProperty(prop)) continue;
        if (modeObj.hasOwnProperty(prop)) modeObj["_" + prop] = modeObj[prop];
        modeObj[prop] = exts[prop];
      }
    }
    modeObj.name = spec.name;
    if (spec.helperType) modeObj.helperType = spec.helperType;
    if (spec.modeProps) for (var prop in spec.modeProps)
      modeObj[prop] = spec.modeProps[prop];

    return modeObj;
  };

  // Minimal default mode.
  CodeMirror.defineMode("null", function() {
    return {token: function(stream) {stream.skipToEnd();}};
  });
  CodeMirror.defineMIME("text/plain", "null");

  // This can be used to attach properties to mode objects from
  // outside the actual mode definition.
  var modeExtensions = CodeMirror.modeExtensions = {};
  CodeMirror.extendMode = function(mode, properties) {
    var exts = modeExtensions.hasOwnProperty(mode) ? modeExtensions[mode] : (modeExtensions[mode] = {});
    copyObj(properties, exts);
  };

  // EXTENSIONS

  CodeMirror.defineExtension = function(name, func) {
    CodeMirror.prototype[name] = func;
  };
  CodeMirror.defineDocExtension = function(name, func) {
    Doc.prototype[name] = func;
  };
  CodeMirror.defineOption = option;

  var initHooks = [];
  CodeMirror.defineInitHook = function(f) {initHooks.push(f);};

  var helpers = CodeMirror.helpers = {};
  CodeMirror.registerHelper = function(type, name, value) {
    if (!helpers.hasOwnProperty(type)) helpers[type] = CodeMirror[type] = {_global: []};
    helpers[type][name] = value;
  };
  CodeMirror.registerGlobalHelper = function(type, name, predicate, value) {
    CodeMirror.registerHelper(type, name, value);
    helpers[type]._global.push({pred: predicate, val: value});
  };

  // MODE STATE HANDLING

  // Utility functions for working with state. Exported because nested
  // modes need to do this for their inner modes.

  var copyState = CodeMirror.copyState = function(mode, state) {
    if (state === true) return state;
    if (mode.copyState) return mode.copyState(state);
    var nstate = {};
    for (var n in state) {
      var val = state[n];
      if (val instanceof Array) val = val.concat([]);
      nstate[n] = val;
    }
    return nstate;
  };

  var startState = CodeMirror.startState = function(mode, a1, a2) {
    return mode.startState ? mode.startState(a1, a2) : true;
  };

  // Given a mode and a state (for that mode), find the inner mode and
  // state at the position that the state refers to.
  CodeMirror.innerMode = function(mode, state) {
    while (mode.innerMode) {
      var info = mode.innerMode(state);
      if (!info || info.mode == mode) break;
      state = info.state;
      mode = info.mode;
    }
    return info || {mode: mode, state: state};
  };

  // STANDARD COMMANDS

  // Commands are parameter-less actions that can be performed on an
  // editor, mostly used for keybindings.
  var commands = CodeMirror.commands = {
    selectAll: function(cm) {cm.setSelection(Pos(cm.firstLine(), 0), Pos(cm.lastLine()), sel_dontScroll);},
    singleSelection: function(cm) {
      cm.setSelection(cm.getCursor("anchor"), cm.getCursor("head"), sel_dontScroll);
    },
    killLine: function(cm) {
      deleteNearSelection(cm, function(range) {
        if (range.empty()) {
          var len = getLine(cm.doc, range.head.line).text.length;
          if (range.head.ch == len && range.head.line < cm.lastLine())
            return {from: range.head, to: Pos(range.head.line + 1, 0)};
          else
            return {from: range.head, to: Pos(range.head.line, len)};
        } else {
          return {from: range.from(), to: range.to()};
        }
      });
    },
    deleteLine: function(cm) {
      deleteNearSelection(cm, function(range) {
        return {from: Pos(range.from().line, 0),
                to: clipPos(cm.doc, Pos(range.to().line + 1, 0))};
      });
    },
    delLineLeft: function(cm) {
      deleteNearSelection(cm, function(range) {
        return {from: Pos(range.from().line, 0), to: range.from()};
      });
    },
    delWrappedLineLeft: function(cm) {
      deleteNearSelection(cm, function(range) {
        var top = cm.charCoords(range.head, "div").top + 5;
        var leftPos = cm.coordsChar({left: 0, top: top}, "div");
        return {from: leftPos, to: range.from()};
      });
    },
    delWrappedLineRight: function(cm) {
      deleteNearSelection(cm, function(range) {
        var top = cm.charCoords(range.head, "div").top + 5;
        var rightPos = cm.coordsChar({left: cm.display.lineDiv.offsetWidth + 100, top: top}, "div");
        return {from: range.from(), to: rightPos };
      });
    },
    undo: function(cm) {cm.undo();},
    redo: function(cm) {cm.redo();},
    undoSelection: function(cm) {cm.undoSelection();},
    redoSelection: function(cm) {cm.redoSelection();},
    goDocStart: function(cm) {cm.extendSelection(Pos(cm.firstLine(), 0));},
    goDocEnd: function(cm) {cm.extendSelection(Pos(cm.lastLine()));},
    goLineStart: function(cm) {
      cm.extendSelectionsBy(function(range) { return lineStart(cm, range.head.line); },
                            {origin: "+move", bias: 1});
    },
    goLineStartSmart: function(cm) {
      cm.extendSelectionsBy(function(range) {
        return lineStartSmart(cm, range.head);
      }, {origin: "+move", bias: 1});
    },
    goLineEnd: function(cm) {
      cm.extendSelectionsBy(function(range) { return lineEnd(cm, range.head.line); },
                            {origin: "+move", bias: -1});
    },
    goLineRight: function(cm) {
      cm.extendSelectionsBy(function(range) {
        var top = cm.charCoords(range.head, "div").top + 5;
        return cm.coordsChar({left: cm.display.lineDiv.offsetWidth + 100, top: top}, "div");
      }, sel_move);
    },
    goLineLeft: function(cm) {
      cm.extendSelectionsBy(function(range) {
        var top = cm.charCoords(range.head, "div").top + 5;
        return cm.coordsChar({left: 0, top: top}, "div");
      }, sel_move);
    },
    goLineLeftSmart: function(cm) {
      cm.extendSelectionsBy(function(range) {
        var top = cm.charCoords(range.head, "div").top + 5;
        var pos = cm.coordsChar({left: 0, top: top}, "div");
        if (pos.ch < cm.getLine(pos.line).search(/\S/)) return lineStartSmart(cm, range.head);
        return pos;
      }, sel_move);
    },
    goLineUp: function(cm) {cm.moveV(-1, "line");},
    goLineDown: function(cm) {cm.moveV(1, "line");},
    goPageUp: function(cm) {cm.moveV(-1, "page");},
    goPageDown: function(cm) {cm.moveV(1, "page");},
    goCharLeft: function(cm) {cm.moveH(-1, "char");},
    goCharRight: function(cm) {cm.moveH(1, "char");},
    goColumnLeft: function(cm) {cm.moveH(-1, "column");},
    goColumnRight: function(cm) {cm.moveH(1, "column");},
    goWordLeft: function(cm) {cm.moveH(-1, "word");},
    goGroupRight: function(cm) {cm.moveH(1, "group");},
    goGroupLeft: function(cm) {cm.moveH(-1, "group");},
    goWordRight: function(cm) {cm.moveH(1, "word");},
    delCharBefore: function(cm) {cm.deleteH(-1, "char");},
    delCharAfter: function(cm) {cm.deleteH(1, "char");},
    delWordBefore: function(cm) {cm.deleteH(-1, "word");},
    delWordAfter: function(cm) {cm.deleteH(1, "word");},
    delGroupBefore: function(cm) {cm.deleteH(-1, "group");},
    delGroupAfter: function(cm) {cm.deleteH(1, "group");},
    indentAuto: function(cm) {cm.indentSelection("smart");},
    indentMore: function(cm) {cm.indentSelection("add");},
    indentLess: function(cm) {cm.indentSelection("subtract");},
    insertTab: function(cm) {cm.replaceSelection("\t");},
    insertSoftTab: function(cm) {
      var spaces = [], ranges = cm.listSelections(), tabSize = cm.options.tabSize;
      for (var i = 0; i < ranges.length; i++) {
        var pos = ranges[i].from();
        var col = countColumn(cm.getLine(pos.line), pos.ch, tabSize);
        spaces.push(spaceStr(tabSize - col % tabSize));
      }
      cm.replaceSelections(spaces);
    },
    defaultTab: function(cm) {
      if (cm.somethingSelected()) cm.indentSelection("add");
      else cm.execCommand("insertTab");
    },
    transposeChars: function(cm) {
      runInOp(cm, function() {
        var ranges = cm.listSelections(), newSel = [];
        for (var i = 0; i < ranges.length; i++) {
          var cur = ranges[i].head, line = getLine(cm.doc, cur.line).text;
          if (line) {
            if (cur.ch == line.length) cur = new Pos(cur.line, cur.ch - 1);
            if (cur.ch > 0) {
              cur = new Pos(cur.line, cur.ch + 1);
              cm.replaceRange(line.charAt(cur.ch - 1) + line.charAt(cur.ch - 2),
                              Pos(cur.line, cur.ch - 2), cur, "+transpose");
            } else if (cur.line > cm.doc.first) {
              var prev = getLine(cm.doc, cur.line - 1).text;
              if (prev)
                cm.replaceRange(line.charAt(0) + cm.doc.lineSeparator() +
                                prev.charAt(prev.length - 1),
                                Pos(cur.line - 1, prev.length - 1), Pos(cur.line, 1), "+transpose");
            }
          }
          newSel.push(new Range(cur, cur));
        }
        cm.setSelections(newSel);
      });
    },
    newlineAndIndent: function(cm) {
      runInOp(cm, function() {
        var len = cm.listSelections().length;
        for (var i = 0; i < len; i++) {
          var range = cm.listSelections()[i];
          cm.replaceRange(cm.doc.lineSeparator(), range.anchor, range.head, "+input");
          cm.indentLine(range.from().line + 1, null, true);
        }
        ensureCursorVisible(cm);
      });
    },
    openLine: function(cm) {cm.replaceSelection("\n", "start")},
    toggleOverwrite: function(cm) {cm.toggleOverwrite();}
  };


  // STANDARD KEYMAPS

  var keyMap = CodeMirror.keyMap = {};

  keyMap.basic = {
    "Left": "goCharLeft", "Right": "goCharRight", "Up": "goLineUp", "Down": "goLineDown",
    "End": "goLineEnd", "Home": "goLineStartSmart", "PageUp": "goPageUp", "PageDown": "goPageDown",
    "Delete": "delCharAfter", "Backspace": "delCharBefore", "Shift-Backspace": "delCharBefore",
    "Tab": "defaultTab", "Shift-Tab": "indentAuto",
    "Enter": "newlineAndIndent", "Insert": "toggleOverwrite",
    "Esc": "singleSelection"
  };
  // Note that the save and find-related commands aren't defined by
  // default. User code or addons can define them. Unknown commands
  // are simply ignored.
  keyMap.pcDefault = {
    "Ctrl-A": "selectAll", "Ctrl-D": "deleteLine", "Ctrl-Z": "undo", "Shift-Ctrl-Z": "redo", "Ctrl-Y": "redo",
    "Ctrl-Home": "goDocStart", "Ctrl-End": "goDocEnd", "Ctrl-Up": "goLineUp", "Ctrl-Down": "goLineDown",
    "Ctrl-Left": "goGroupLeft", "Ctrl-Right": "goGroupRight", "Alt-Left": "goLineStart", "Alt-Right": "goLineEnd",
    "Ctrl-Backspace": "delGroupBefore", "Ctrl-Delete": "delGroupAfter", "Ctrl-S": "save", "Ctrl-F": "find",
    "Ctrl-G": "findNext", "Shift-Ctrl-G": "findPrev", "Shift-Ctrl-F": "replace", "Shift-Ctrl-R": "replaceAll",
    "Ctrl-[": "indentLess", "Ctrl-]": "indentMore",
    "Ctrl-U": "undoSelection", "Shift-Ctrl-U": "redoSelection", "Alt-U": "redoSelection",
    fallthrough: "basic"
  };
  // Very basic readline/emacs-style bindings, which are standard on Mac.
  keyMap.emacsy = {
    "Ctrl-F": "goCharRight", "Ctrl-B": "goCharLeft", "Ctrl-P": "goLineUp", "Ctrl-N": "goLineDown",
    "Alt-F": "goWordRight", "Alt-B": "goWordLeft", "Ctrl-A": "goLineStart", "Ctrl-E": "goLineEnd",
    "Ctrl-V": "goPageDown", "Shift-Ctrl-V": "goPageUp", "Ctrl-D": "delCharAfter", "Ctrl-H": "delCharBefore",
    "Alt-D": "delWordAfter", "Alt-Backspace": "delWordBefore", "Ctrl-K": "killLine", "Ctrl-T": "transposeChars",
    "Ctrl-O": "openLine"
  };
  keyMap.macDefault = {
    "Cmd-A": "selectAll", "Cmd-D": "deleteLine", "Cmd-Z": "undo", "Shift-Cmd-Z": "redo", "Cmd-Y": "redo",
    "Cmd-Home": "goDocStart", "Cmd-Up": "goDocStart", "Cmd-End": "goDocEnd", "Cmd-Down": "goDocEnd", "Alt-Left": "goGroupLeft",
    "Alt-Right": "goGroupRight", "Cmd-Left": "goLineLeft", "Cmd-Right": "goLineRight", "Alt-Backspace": "delGroupBefore",
    "Ctrl-Alt-Backspace": "delGroupAfter", "Alt-Delete": "delGroupAfter", "Cmd-S": "save", "Cmd-F": "find",
    "Cmd-G": "findNext", "Shift-Cmd-G": "findPrev", "Cmd-Alt-F": "replace", "Shift-Cmd-Alt-F": "replaceAll",
    "Cmd-[": "indentLess", "Cmd-]": "indentMore", "Cmd-Backspace": "delWrappedLineLeft", "Cmd-Delete": "delWrappedLineRight",
    "Cmd-U": "undoSelection", "Shift-Cmd-U": "redoSelection", "Ctrl-Up": "goDocStart", "Ctrl-Down": "goDocEnd",
    fallthrough: ["basic", "emacsy"]
  };
  keyMap["default"] = mac ? keyMap.macDefault : keyMap.pcDefault;

  // KEYMAP DISPATCH

  function normalizeKeyName(name) {
    var parts = name.split(/-(?!$)/), name = parts[parts.length - 1];
    var alt, ctrl, shift, cmd;
    for (var i = 0; i < parts.length - 1; i++) {
      var mod = parts[i];
      if (/^(cmd|meta|m)$/i.test(mod)) cmd = true;
      else if (/^a(lt)?$/i.test(mod)) alt = true;
      else if (/^(c|ctrl|control)$/i.test(mod)) ctrl = true;
      else if (/^s(hift)$/i.test(mod)) shift = true;
      else throw new Error("Unrecognized modifier name: " + mod);
    }
    if (alt) name = "Alt-" + name;
    if (ctrl) name = "Ctrl-" + name;
    if (cmd) name = "Cmd-" + name;
    if (shift) name = "Shift-" + name;
    return name;
  }

  // This is a kludge to keep keymaps mostly working as raw objects
  // (backwards compatibility) while at the same time support features
  // like normalization and multi-stroke key bindings. It compiles a
  // new normalized keymap, and then updates the old object to reflect
  // this.
  CodeMirror.normalizeKeyMap = function(keymap) {
    var copy = {};
    for (var keyname in keymap) if (keymap.hasOwnProperty(keyname)) {
      var value = keymap[keyname];
      if (/^(name|fallthrough|(de|at)tach)$/.test(keyname)) continue;
      if (value == "...") { delete keymap[keyname]; continue; }

      var keys = map(keyname.split(" "), normalizeKeyName);
      for (var i = 0; i < keys.length; i++) {
        var val, name;
        if (i == keys.length - 1) {
          name = keys.join(" ");
          val = value;
        } else {
          name = keys.slice(0, i + 1).join(" ");
          val = "...";
        }
        var prev = copy[name];
        if (!prev) copy[name] = val;
        else if (prev != val) throw new Error("Inconsistent bindings for " + name);
      }
      delete keymap[keyname];
    }
    for (var prop in copy) keymap[prop] = copy[prop];
    return keymap;
  };

  var lookupKey = CodeMirror.lookupKey = function(key, map, handle, context) {
    map = getKeyMap(map);
    var found = map.call ? map.call(key, context) : map[key];
    if (found === false) return "nothing";
    if (found === "...") return "multi";
    if (found != null && handle(found)) return "handled";

    if (map.fallthrough) {
      if (Object.prototype.toString.call(map.fallthrough) != "[object Array]")
        return lookupKey(key, map.fallthrough, handle, context);
      for (var i = 0; i < map.fallthrough.length; i++) {
        var result = lookupKey(key, map.fallthrough[i], handle, context);
        if (result) return result;
      }
    }
  };

  // Modifier key presses don't count as 'real' key presses for the
  // purpose of keymap fallthrough.
  var isModifierKey = CodeMirror.isModifierKey = function(value) {
    var name = typeof value == "string" ? value : keyNames[value.keyCode];
    return name == "Ctrl" || name == "Alt" || name == "Shift" || name == "Mod";
  };

  // Look up the name of a key as indicated by an event object.
  var keyName = CodeMirror.keyName = function(event, noShift) {
    if (presto && event.keyCode == 34 && event["char"]) return false;
    var base = keyNames[event.keyCode], name = base;
    if (name == null || event.altGraphKey) return false;
    if (event.altKey && base != "Alt") name = "Alt-" + name;
    if ((flipCtrlCmd ? event.metaKey : event.ctrlKey) && base != "Ctrl") name = "Ctrl-" + name;
    if ((flipCtrlCmd ? event.ctrlKey : event.metaKey) && base != "Cmd") name = "Cmd-" + name;
    if (!noShift && event.shiftKey && base != "Shift") name = "Shift-" + name;
    return name;
  };

  function getKeyMap(val) {
    return typeof val == "string" ? keyMap[val] : val;
  }

  // FROMTEXTAREA

  CodeMirror.fromTextArea = function(textarea, options) {
    options = options ? copyObj(options) : {};
    options.value = textarea.value;
    if (!options.tabindex && textarea.tabIndex)
      options.tabindex = textarea.tabIndex;
    if (!options.placeholder && textarea.placeholder)
      options.placeholder = textarea.placeholder;
    // Set autofocus to true if this textarea is focused, or if it has
    // autofocus and no other element is focused.
    if (options.autofocus == null) {
      var hasFocus = activeElt();
      options.autofocus = hasFocus == textarea ||
        textarea.getAttribute("autofocus") != null && hasFocus == document.body;
    }

    function save() {textarea.value = cm.getValue();}
    if (textarea.form) {
      on(textarea.form, "submit", save);
      // Deplorable hack to make the submit method do the right thing.
      if (!options.leaveSubmitMethodAlone) {
        var form = textarea.form, realSubmit = form.submit;
        try {
          var wrappedSubmit = form.submit = function() {
            save();
            form.submit = realSubmit;
            form.submit();
            form.submit = wrappedSubmit;
          };
        } catch(e) {}
      }
    }

    options.finishInit = function(cm) {
      cm.save = save;
      cm.getTextArea = function() { return textarea; };
      cm.toTextArea = function() {
        cm.toTextArea = isNaN; // Prevent this from being ran twice
        save();
        textarea.parentNode.removeChild(cm.getWrapperElement());
        textarea.style.display = "";
        if (textarea.form) {
          off(textarea.form, "submit", save);
          if (typeof textarea.form.submit == "function")
            textarea.form.submit = realSubmit;
        }
      };
    };

    textarea.style.display = "none";
    var cm = CodeMirror(function(node) {
      textarea.parentNode.insertBefore(node, textarea.nextSibling);
    }, options);
    return cm;
  };

  // STRING STREAM

  // Fed to the mode parsers, provides helper functions to make
  // parsers more succinct.

  var StringStream = CodeMirror.StringStream = function(string, tabSize) {
    this.pos = this.start = 0;
    this.string = string;
    this.tabSize = tabSize || 8;
    this.lastColumnPos = this.lastColumnValue = 0;
    this.lineStart = 0;
  };

  StringStream.prototype = {
    eol: function() {return this.pos >= this.string.length;},
    sol: function() {return this.pos == this.lineStart;},
    peek: function() {return this.string.charAt(this.pos) || undefined;},
    next: function() {
      if (this.pos < this.string.length)
        return this.string.charAt(this.pos++);
    },
    eat: function(match) {
      var ch = this.string.charAt(this.pos);
      if (typeof match == "string") var ok = ch == match;
      else var ok = ch && (match.test ? match.test(ch) : match(ch));
      if (ok) {++this.pos; return ch;}
    },
    eatWhile: function(match) {
      var start = this.pos;
      while (this.eat(match)){}
      return this.pos > start;
    },
    eatSpace: function() {
      var start = this.pos;
      while (/[\s\u00a0]/.test(this.string.charAt(this.pos))) ++this.pos;
      return this.pos > start;
    },
    skipToEnd: function() {this.pos = this.string.length;},
    skipTo: function(ch) {
      var found = this.string.indexOf(ch, this.pos);
      if (found > -1) {this.pos = found; return true;}
    },
    backUp: function(n) {this.pos -= n;},
    column: function() {
      if (this.lastColumnPos < this.start) {
        this.lastColumnValue = countColumn(this.string, this.start, this.tabSize, this.lastColumnPos, this.lastColumnValue);
        this.lastColumnPos = this.start;
      }
      return this.lastColumnValue - (this.lineStart ? countColumn(this.string, this.lineStart, this.tabSize) : 0);
    },
    indentation: function() {
      return countColumn(this.string, null, this.tabSize) -
        (this.lineStart ? countColumn(this.string, this.lineStart, this.tabSize) : 0);
    },
    match: function(pattern, consume, caseInsensitive) {
      if (typeof pattern == "string") {
        var cased = function(str) {return caseInsensitive ? str.toLowerCase() : str;};
        var substr = this.string.substr(this.pos, pattern.length);
        if (cased(substr) == cased(pattern)) {
          if (consume !== false) this.pos += pattern.length;
          return true;
        }
      } else {
        var match = this.string.slice(this.pos).match(pattern);
        if (match && match.index > 0) return null;
        if (match && consume !== false) this.pos += match[0].length;
        return match;
      }
    },
    current: function(){return this.string.slice(this.start, this.pos);},
    hideFirstChars: function(n, inner) {
      this.lineStart += n;
      try { return inner(); }
      finally { this.lineStart -= n; }
    }
  };

  // TEXTMARKERS

  // Created with markText and setBookmark methods. A TextMarker is a
  // handle that can be used to clear or find a marked position in the
  // document. Line objects hold arrays (markedSpans) containing
  // {from, to, marker} object pointing to such marker objects, and
  // indicating that such a marker is present on that line. Multiple
  // lines may point to the same marker when it spans across lines.
  // The spans will have null for their from/to properties when the
  // marker continues beyond the start/end of the line. Markers have
  // links back to the lines they currently touch.

  var nextMarkerId = 0;

  var TextMarker = CodeMirror.TextMarker = function(doc, type) {
    this.lines = [];
    this.type = type;
    this.doc = doc;
    this.id = ++nextMarkerId;
  };
  eventMixin(TextMarker);

  // Clear the marker.
  TextMarker.prototype.clear = function() {
    if (this.explicitlyCleared) return;
    var cm = this.doc.cm, withOp = cm && !cm.curOp;
    if (withOp) startOperation(cm);
    if (hasHandler(this, "clear")) {
      var found = this.find();
      if (found) signalLater(this, "clear", found.from, found.to);
    }
    var min = null, max = null;
    for (var i = 0; i < this.lines.length; ++i) {
      var line = this.lines[i];
      var span = getMarkedSpanFor(line.markedSpans, this);
      if (cm && !this.collapsed) regLineChange(cm, lineNo(line), "text");
      else if (cm) {
        if (span.to != null) max = lineNo(line);
        if (span.from != null) min = lineNo(line);
      }
      line.markedSpans = removeMarkedSpan(line.markedSpans, span);
      if (span.from == null && this.collapsed && !lineIsHidden(this.doc, line) && cm)
        updateLineHeight(line, textHeight(cm.display));
    }
    if (cm && this.collapsed && !cm.options.lineWrapping) for (var i = 0; i < this.lines.length; ++i) {
      var visual = visualLine(this.lines[i]), len = lineLength(visual);
      if (len > cm.display.maxLineLength) {
        cm.display.maxLine = visual;
        cm.display.maxLineLength = len;
        cm.display.maxLineChanged = true;
      }
    }

    if (min != null && cm && this.collapsed) regChange(cm, min, max + 1);
    this.lines.length = 0;
    this.explicitlyCleared = true;
    if (this.atomic && this.doc.cantEdit) {
      this.doc.cantEdit = false;
      if (cm) reCheckSelection(cm.doc);
    }
    if (cm) signalLater(cm, "markerCleared", cm, this);
    if (withOp) endOperation(cm);
    if (this.parent) this.parent.clear();
  };

  // Find the position of the marker in the document. Returns a {from,
  // to} object by default. Side can be passed to get a specific side
  // -- 0 (both), -1 (left), or 1 (right). When lineObj is true, the
  // Pos objects returned contain a line object, rather than a line
  // number (used to prevent looking up the same line twice).
  TextMarker.prototype.find = function(side, lineObj) {
    if (side == null && this.type == "bookmark") side = 1;
    var from, to;
    for (var i = 0; i < this.lines.length; ++i) {
      var line = this.lines[i];
      var span = getMarkedSpanFor(line.markedSpans, this);
      if (span.from != null) {
        from = Pos(lineObj ? line : lineNo(line), span.from);
        if (side == -1) return from;
      }
      if (span.to != null) {
        to = Pos(lineObj ? line : lineNo(line), span.to);
        if (side == 1) return to;
      }
    }
    return from && {from: from, to: to};
  };

  // Signals that the marker's widget changed, and surrounding layout
  // should be recomputed.
  TextMarker.prototype.changed = function() {
    var pos = this.find(-1, true), widget = this, cm = this.doc.cm;
    if (!pos || !cm) return;
    runInOp(cm, function() {
      var line = pos.line, lineN = lineNo(pos.line);
      var view = findViewForLine(cm, lineN);
      if (view) {
        clearLineMeasurementCacheFor(view);
        cm.curOp.selectionChanged = cm.curOp.forceUpdate = true;
      }
      cm.curOp.updateMaxLine = true;
      if (!lineIsHidden(widget.doc, line) && widget.height != null) {
        var oldHeight = widget.height;
        widget.height = null;
        var dHeight = widgetHeight(widget) - oldHeight;
        if (dHeight)
          updateLineHeight(line, line.height + dHeight);
      }
    });
  };

  TextMarker.prototype.attachLine = function(line) {
    if (!this.lines.length && this.doc.cm) {
      var op = this.doc.cm.curOp;
      if (!op.maybeHiddenMarkers || indexOf(op.maybeHiddenMarkers, this) == -1)
        (op.maybeUnhiddenMarkers || (op.maybeUnhiddenMarkers = [])).push(this);
    }
    this.lines.push(line);
  };
  TextMarker.prototype.detachLine = function(line) {
    this.lines.splice(indexOf(this.lines, line), 1);
    if (!this.lines.length && this.doc.cm) {
      var op = this.doc.cm.curOp;
      (op.maybeHiddenMarkers || (op.maybeHiddenMarkers = [])).push(this);
    }
  };

  // Collapsed markers have unique ids, in order to be able to order
  // them, which is needed for uniquely determining an outer marker
  // when they overlap (they may nest, but not partially overlap).
  var nextMarkerId = 0;

  // Create a marker, wire it up to the right lines, and
  function markText(doc, from, to, options, type) {
    // Shared markers (across linked documents) are handled separately
    // (markTextShared will call out to this again, once per
    // document).
    if (options && options.shared) return markTextShared(doc, from, to, options, type);
    // Ensure we are in an operation.
    if (doc.cm && !doc.cm.curOp) return operation(doc.cm, markText)(doc, from, to, options, type);

    var marker = new TextMarker(doc, type), diff = cmp(from, to);
    if (options) copyObj(options, marker, false);
    // Don't connect empty markers unless clearWhenEmpty is false
    if (diff > 0 || diff == 0 && marker.clearWhenEmpty !== false)
      return marker;
    if (marker.replacedWith) {
      // Showing up as a widget implies collapsed (widget replaces text)
      marker.collapsed = true;
      marker.widgetNode = elt("span", [marker.replacedWith], "CodeMirror-widget");
      if (!options.handleMouseEvents) marker.widgetNode.setAttribute("cm-ignore-events", "true");
      if (options.insertLeft) marker.widgetNode.insertLeft = true;
    }
    if (marker.collapsed) {
      if (conflictingCollapsedRange(doc, from.line, from, to, marker) ||
          from.line != to.line && conflictingCollapsedRange(doc, to.line, from, to, marker))
        throw new Error("Inserting collapsed marker partially overlapping an existing one");
      sawCollapsedSpans = true;
    }

    if (marker.addToHistory)
      addChangeToHistory(doc, {from: from, to: to, origin: "markText"}, doc.sel, NaN);

    var curLine = from.line, cm = doc.cm, updateMaxLine;
    doc.iter(curLine, to.line + 1, function(line) {
      if (cm && marker.collapsed && !cm.options.lineWrapping && visualLine(line) == cm.display.maxLine)
        updateMaxLine = true;
      if (marker.collapsed && curLine != from.line) updateLineHeight(line, 0);
      addMarkedSpan(line, new MarkedSpan(marker,
                                         curLine == from.line ? from.ch : null,
                                         curLine == to.line ? to.ch : null));
      ++curLine;
    });
    // lineIsHidden depends on the presence of the spans, so needs a second pass
    if (marker.collapsed) doc.iter(from.line, to.line + 1, function(line) {
      if (lineIsHidden(doc, line)) updateLineHeight(line, 0);
    });

    if (marker.clearOnEnter) on(marker, "beforeCursorEnter", function() { marker.clear(); });

    if (marker.readOnly) {
      sawReadOnlySpans = true;
      if (doc.history.done.length || doc.history.undone.length)
        doc.clearHistory();
    }
    if (marker.collapsed) {
      marker.id = ++nextMarkerId;
      marker.atomic = true;
    }
    if (cm) {
      // Sync editor state
      if (updateMaxLine) cm.curOp.updateMaxLine = true;
      if (marker.collapsed)
        regChange(cm, from.line, to.line + 1);
      else if (marker.className || marker.title || marker.startStyle || marker.endStyle || marker.css)
        for (var i = from.line; i <= to.line; i++) regLineChange(cm, i, "text");
      if (marker.atomic) reCheckSelection(cm.doc);
      signalLater(cm, "markerAdded", cm, marker);
    }
    return marker;
  }

  // SHARED TEXTMARKERS

  // A shared marker spans multiple linked documents. It is
  // implemented as a meta-marker-object controlling multiple normal
  // markers.
  var SharedTextMarker = CodeMirror.SharedTextMarker = function(markers, primary) {
    this.markers = markers;
    this.primary = primary;
    for (var i = 0; i < markers.length; ++i)
      markers[i].parent = this;
  };
  eventMixin(SharedTextMarker);

  SharedTextMarker.prototype.clear = function() {
    if (this.explicitlyCleared) return;
    this.explicitlyCleared = true;
    for (var i = 0; i < this.markers.length; ++i)
      this.markers[i].clear();
    signalLater(this, "clear");
  };
  SharedTextMarker.prototype.find = function(side, lineObj) {
    return this.primary.find(side, lineObj);
  };

  function markTextShared(doc, from, to, options, type) {
    options = copyObj(options);
    options.shared = false;
    var markers = [markText(doc, from, to, options, type)], primary = markers[0];
    var widget = options.widgetNode;
    linkedDocs(doc, function(doc) {
      if (widget) options.widgetNode = widget.cloneNode(true);
      markers.push(markText(doc, clipPos(doc, from), clipPos(doc, to), options, type));
      for (var i = 0; i < doc.linked.length; ++i)
        if (doc.linked[i].isParent) return;
      primary = lst(markers);
    });
    return new SharedTextMarker(markers, primary);
  }

  function findSharedMarkers(doc) {
    return doc.findMarks(Pos(doc.first, 0), doc.clipPos(Pos(doc.lastLine())),
                         function(m) { return m.parent; });
  }

  function copySharedMarkers(doc, markers) {
    for (var i = 0; i < markers.length; i++) {
      var marker = markers[i], pos = marker.find();
      var mFrom = doc.clipPos(pos.from), mTo = doc.clipPos(pos.to);
      if (cmp(mFrom, mTo)) {
        var subMark = markText(doc, mFrom, mTo, marker.primary, marker.primary.type);
        marker.markers.push(subMark);
        subMark.parent = marker;
      }
    }
  }

  function detachSharedMarkers(markers) {
    for (var i = 0; i < markers.length; i++) {
      var marker = markers[i], linked = [marker.primary.doc];;
      linkedDocs(marker.primary.doc, function(d) { linked.push(d); });
      for (var j = 0; j < marker.markers.length; j++) {
        var subMarker = marker.markers[j];
        if (indexOf(linked, subMarker.doc) == -1) {
          subMarker.parent = null;
          marker.markers.splice(j--, 1);
        }
      }
    }
  }

  // TEXTMARKER SPANS

  function MarkedSpan(marker, from, to) {
    this.marker = marker;
    this.from = from; this.to = to;
  }

  // Search an array of spans for a span matching the given marker.
  function getMarkedSpanFor(spans, marker) {
    if (spans) for (var i = 0; i < spans.length; ++i) {
      var span = spans[i];
      if (span.marker == marker) return span;
    }
  }
  // Remove a span from an array, returning undefined if no spans are
  // left (we don't store arrays for lines without spans).
  function removeMarkedSpan(spans, span) {
    for (var r, i = 0; i < spans.length; ++i)
      if (spans[i] != span) (r || (r = [])).push(spans[i]);
    return r;
  }
  // Add a span to a line.
  function addMarkedSpan(line, span) {
    line.markedSpans = line.markedSpans ? line.markedSpans.concat([span]) : [span];
    span.marker.attachLine(line);
  }

  // Used for the algorithm that adjusts markers for a change in the
  // document. These functions cut an array of spans at a given
  // character position, returning an array of remaining chunks (or
  // undefined if nothing remains).
  function markedSpansBefore(old, startCh, isInsert) {
    if (old) for (var i = 0, nw; i < old.length; ++i) {
      var span = old[i], marker = span.marker;
      var startsBefore = span.from == null || (marker.inclusiveLeft ? span.from <= startCh : span.from < startCh);
      if (startsBefore || span.from == startCh && marker.type == "bookmark" && (!isInsert || !span.marker.insertLeft)) {
        var endsAfter = span.to == null || (marker.inclusiveRight ? span.to >= startCh : span.to > startCh);
        (nw || (nw = [])).push(new MarkedSpan(marker, span.from, endsAfter ? null : span.to));
      }
    }
    return nw;
  }
  function markedSpansAfter(old, endCh, isInsert) {
    if (old) for (var i = 0, nw; i < old.length; ++i) {
      var span = old[i], marker = span.marker;
      var endsAfter = span.to == null || (marker.inclusiveRight ? span.to >= endCh : span.to > endCh);
      if (endsAfter || span.from == endCh && marker.type == "bookmark" && (!isInsert || span.marker.insertLeft)) {
        var startsBefore = span.from == null || (marker.inclusiveLeft ? span.from <= endCh : span.from < endCh);
        (nw || (nw = [])).push(new MarkedSpan(marker, startsBefore ? null : span.from - endCh,
                                              span.to == null ? null : span.to - endCh));
      }
    }
    return nw;
  }

  // Given a change object, compute the new set of marker spans that
  // cover the line in which the change took place. Removes spans
  // entirely within the change, reconnects spans belonging to the
  // same marker that appear on both sides of the change, and cuts off
  // spans partially within the change. Returns an array of span
  // arrays with one element for each line in (after) the change.
  function stretchSpansOverChange(doc, change) {
    if (change.full) return null;
    var oldFirst = isLine(doc, change.from.line) && getLine(doc, change.from.line).markedSpans;
    var oldLast = isLine(doc, change.to.line) && getLine(doc, change.to.line).markedSpans;
    if (!oldFirst && !oldLast) return null;

    var startCh = change.from.ch, endCh = change.to.ch, isInsert = cmp(change.from, change.to) == 0;
    // Get the spans that 'stick out' on both sides
    var first = markedSpansBefore(oldFirst, startCh, isInsert);
    var last = markedSpansAfter(oldLast, endCh, isInsert);

    // Next, merge those two ends
    var sameLine = change.text.length == 1, offset = lst(change.text).length + (sameLine ? startCh : 0);
    if (first) {
      // Fix up .to properties of first
      for (var i = 0; i < first.length; ++i) {
        var span = first[i];
        if (span.to == null) {
          var found = getMarkedSpanFor(last, span.marker);
          if (!found) span.to = startCh;
          else if (sameLine) span.to = found.to == null ? null : found.to + offset;
        }
      }
    }
    if (last) {
      // Fix up .from in last (or move them into first in case of sameLine)
      for (var i = 0; i < last.length; ++i) {
        var span = last[i];
        if (span.to != null) span.to += offset;
        if (span.from == null) {
          var found = getMarkedSpanFor(first, span.marker);
          if (!found) {
            span.from = offset;
            if (sameLine) (first || (first = [])).push(span);
          }
        } else {
          span.from += offset;
          if (sameLine) (first || (first = [])).push(span);
        }
      }
    }
    // Make sure we didn't create any zero-length spans
    if (first) first = clearEmptySpans(first);
    if (last && last != first) last = clearEmptySpans(last);

    var newMarkers = [first];
    if (!sameLine) {
      // Fill gap with whole-line-spans
      var gap = change.text.length - 2, gapMarkers;
      if (gap > 0 && first)
        for (var i = 0; i < first.length; ++i)
          if (first[i].to == null)
            (gapMarkers || (gapMarkers = [])).push(new MarkedSpan(first[i].marker, null, null));
      for (var i = 0; i < gap; ++i)
        newMarkers.push(gapMarkers);
      newMarkers.push(last);
    }
    return newMarkers;
  }

  // Remove spans that are empty and don't have a clearWhenEmpty
  // option of false.
  function clearEmptySpans(spans) {
    for (var i = 0; i < spans.length; ++i) {
      var span = spans[i];
      if (span.from != null && span.from == span.to && span.marker.clearWhenEmpty !== false)
        spans.splice(i--, 1);
    }
    if (!spans.length) return null;
    return spans;
  }

  // Used for un/re-doing changes from the history. Combines the
  // result of computing the existing spans with the set of spans that
  // existed in the history (so that deleting around a span and then
  // undoing brings back the span).
  function mergeOldSpans(doc, change) {
    var old = getOldSpans(doc, change);
    var stretched = stretchSpansOverChange(doc, change);
    if (!old) return stretched;
    if (!stretched) return old;

    for (var i = 0; i < old.length; ++i) {
      var oldCur = old[i], stretchCur = stretched[i];
      if (oldCur && stretchCur) {
        spans: for (var j = 0; j < stretchCur.length; ++j) {
          var span = stretchCur[j];
          for (var k = 0; k < oldCur.length; ++k)
            if (oldCur[k].marker == span.marker) continue spans;
          oldCur.push(span);
        }
      } else if (stretchCur) {
        old[i] = stretchCur;
      }
    }
    return old;
  }

  // Used to 'clip' out readOnly ranges when making a change.
  function removeReadOnlyRanges(doc, from, to) {
    var markers = null;
    doc.iter(from.line, to.line + 1, function(line) {
      if (line.markedSpans) for (var i = 0; i < line.markedSpans.length; ++i) {
        var mark = line.markedSpans[i].marker;
        if (mark.readOnly && (!markers || indexOf(markers, mark) == -1))
          (markers || (markers = [])).push(mark);
      }
    });
    if (!markers) return null;
    var parts = [{from: from, to: to}];
    for (var i = 0; i < markers.length; ++i) {
      var mk = markers[i], m = mk.find(0);
      for (var j = 0; j < parts.length; ++j) {
        var p = parts[j];
        if (cmp(p.to, m.from) < 0 || cmp(p.from, m.to) > 0) continue;
        var newParts = [j, 1], dfrom = cmp(p.from, m.from), dto = cmp(p.to, m.to);
        if (dfrom < 0 || !mk.inclusiveLeft && !dfrom)
          newParts.push({from: p.from, to: m.from});
        if (dto > 0 || !mk.inclusiveRight && !dto)
          newParts.push({from: m.to, to: p.to});
        parts.splice.apply(parts, newParts);
        j += newParts.length - 1;
      }
    }
    return parts;
  }

  // Connect or disconnect spans from a line.
  function detachMarkedSpans(line) {
    var spans = line.markedSpans;
    if (!spans) return;
    for (var i = 0; i < spans.length; ++i)
      spans[i].marker.detachLine(line);
    line.markedSpans = null;
  }
  function attachMarkedSpans(line, spans) {
    if (!spans) return;
    for (var i = 0; i < spans.length; ++i)
      spans[i].marker.attachLine(line);
    line.markedSpans = spans;
  }

  // Helpers used when computing which overlapping collapsed span
  // counts as the larger one.
  function extraLeft(marker) { return marker.inclusiveLeft ? -1 : 0; }
  function extraRight(marker) { return marker.inclusiveRight ? 1 : 0; }

  // Returns a number indicating which of two overlapping collapsed
  // spans is larger (and thus includes the other). Falls back to
  // comparing ids when the spans cover exactly the same range.
  function compareCollapsedMarkers(a, b) {
    var lenDiff = a.lines.length - b.lines.length;
    if (lenDiff != 0) return lenDiff;
    var aPos = a.find(), bPos = b.find();
    var fromCmp = cmp(aPos.from, bPos.from) || extraLeft(a) - extraLeft(b);
    if (fromCmp) return -fromCmp;
    var toCmp = cmp(aPos.to, bPos.to) || extraRight(a) - extraRight(b);
    if (toCmp) return toCmp;
    return b.id - a.id;
  }

  // Find out whether a line ends or starts in a collapsed span. If
  // so, return the marker for that span.
  function collapsedSpanAtSide(line, start) {
    var sps = sawCollapsedSpans && line.markedSpans, found;
    if (sps) for (var sp, i = 0; i < sps.length; ++i) {
      sp = sps[i];
      if (sp.marker.collapsed && (start ? sp.from : sp.to) == null &&
          (!found || compareCollapsedMarkers(found, sp.marker) < 0))
        found = sp.marker;
    }
    return found;
  }
  function collapsedSpanAtStart(line) { return collapsedSpanAtSide(line, true); }
  function collapsedSpanAtEnd(line) { return collapsedSpanAtSide(line, false); }

  // Test whether there exists a collapsed span that partially
  // overlaps (covers the start or end, but not both) of a new span.
  // Such overlap is not allowed.
  function conflictingCollapsedRange(doc, lineNo, from, to, marker) {
    var line = getLine(doc, lineNo);
    var sps = sawCollapsedSpans && line.markedSpans;
    if (sps) for (var i = 0; i < sps.length; ++i) {
      var sp = sps[i];
      if (!sp.marker.collapsed) continue;
      var found = sp.marker.find(0);
      var fromCmp = cmp(found.from, from) || extraLeft(sp.marker) - extraLeft(marker);
      var toCmp = cmp(found.to, to) || extraRight(sp.marker) - extraRight(marker);
      if (fromCmp >= 0 && toCmp <= 0 || fromCmp <= 0 && toCmp >= 0) continue;
      if (fromCmp <= 0 && (sp.marker.inclusiveRight && marker.inclusiveLeft ? cmp(found.to, from) >= 0 : cmp(found.to, from) > 0) ||
          fromCmp >= 0 && (sp.marker.inclusiveRight && marker.inclusiveLeft ? cmp(found.from, to) <= 0 : cmp(found.from, to) < 0))
        return true;
    }
  }

  // A visual line is a line as drawn on the screen. Folding, for
  // example, can cause multiple logical lines to appear on the same
  // visual line. This finds the start of the visual line that the
  // given line is part of (usually that is the line itself).
  function visualLine(line) {
    var merged;
    while (merged = collapsedSpanAtStart(line))
      line = merged.find(-1, true).line;
    return line;
  }

  // Returns an array of logical lines that continue the visual line
  // started by the argument, or undefined if there are no such lines.
  function visualLineContinued(line) {
    var merged, lines;
    while (merged = collapsedSpanAtEnd(line)) {
      line = merged.find(1, true).line;
      (lines || (lines = [])).push(line);
    }
    return lines;
  }

  // Get the line number of the start of the visual line that the
  // given line number is part of.
  function visualLineNo(doc, lineN) {
    var line = getLine(doc, lineN), vis = visualLine(line);
    if (line == vis) return lineN;
    return lineNo(vis);
  }
  // Get the line number of the start of the next visual line after
  // the given line.
  function visualLineEndNo(doc, lineN) {
    if (lineN > doc.lastLine()) return lineN;
    var line = getLine(doc, lineN), merged;
    if (!lineIsHidden(doc, line)) return lineN;
    while (merged = collapsedSpanAtEnd(line))
      line = merged.find(1, true).line;
    return lineNo(line) + 1;
  }

  // Compute whether a line is hidden. Lines count as hidden when they
  // are part of a visual line that starts with another line, or when
  // they are entirely covered by collapsed, non-widget span.
  function lineIsHidden(doc, line) {
    var sps = sawCollapsedSpans && line.markedSpans;
    if (sps) for (var sp, i = 0; i < sps.length; ++i) {
      sp = sps[i];
      if (!sp.marker.collapsed) continue;
      if (sp.from == null) return true;
      if (sp.marker.widgetNode) continue;
      if (sp.from == 0 && sp.marker.inclusiveLeft && lineIsHiddenInner(doc, line, sp))
        return true;
    }
  }
  function lineIsHiddenInner(doc, line, span) {
    if (span.to == null) {
      var end = span.marker.find(1, true);
      return lineIsHiddenInner(doc, end.line, getMarkedSpanFor(end.line.markedSpans, span.marker));
    }
    if (span.marker.inclusiveRight && span.to == line.text.length)
      return true;
    for (var sp, i = 0; i < line.markedSpans.length; ++i) {
      sp = line.markedSpans[i];
      if (sp.marker.collapsed && !sp.marker.widgetNode && sp.from == span.to &&
          (sp.to == null || sp.to != span.from) &&
          (sp.marker.inclusiveLeft || span.marker.inclusiveRight) &&
          lineIsHiddenInner(doc, line, sp)) return true;
    }
  }

  // LINE WIDGETS

  // Line widgets are block elements displayed above or below a line.

  var LineWidget = CodeMirror.LineWidget = function(doc, node, options) {
    if (options) for (var opt in options) if (options.hasOwnProperty(opt))
      this[opt] = options[opt];
    this.doc = doc;
    this.node = node;
  };
  eventMixin(LineWidget);

  function adjustScrollWhenAboveVisible(cm, line, diff) {
    if (heightAtLine(line) < ((cm.curOp && cm.curOp.scrollTop) || cm.doc.scrollTop))
      addToScrollPos(cm, null, diff);
  }

  LineWidget.prototype.clear = function() {
    var cm = this.doc.cm, ws = this.line.widgets, line = this.line, no = lineNo(line);
    if (no == null || !ws) return;
    for (var i = 0; i < ws.length; ++i) if (ws[i] == this) ws.splice(i--, 1);
    if (!ws.length) line.widgets = null;
    var height = widgetHeight(this);
    updateLineHeight(line, Math.max(0, line.height - height));
    if (cm) runInOp(cm, function() {
      adjustScrollWhenAboveVisible(cm, line, -height);
      regLineChange(cm, no, "widget");
    });
  };
  LineWidget.prototype.changed = function() {
    var oldH = this.height, cm = this.doc.cm, line = this.line;
    this.height = null;
    var diff = widgetHeight(this) - oldH;
    if (!diff) return;
    updateLineHeight(line, line.height + diff);
    if (cm) runInOp(cm, function() {
      cm.curOp.forceUpdate = true;
      adjustScrollWhenAboveVisible(cm, line, diff);
    });
  };

  function widgetHeight(widget) {
    if (widget.height != null) return widget.height;
    var cm = widget.doc.cm;
    if (!cm) return 0;
    if (!contains(document.body, widget.node)) {
      var parentStyle = "position: relative;";
      if (widget.coverGutter)
        parentStyle += "margin-left: -" + cm.display.gutters.offsetWidth + "px;";
      if (widget.noHScroll)
        parentStyle += "width: " + cm.display.wrapper.clientWidth + "px;";
      removeChildrenAndAdd(cm.display.measure, elt("div", [widget.node], null, parentStyle));
    }
    return widget.height = widget.node.parentNode.offsetHeight;
  }

  function addLineWidget(doc, handle, node, options) {
    var widget = new LineWidget(doc, node, options);
    var cm = doc.cm;
    if (cm && widget.noHScroll) cm.display.alignWidgets = true;
    changeLine(doc, handle, "widget", function(line) {
      var widgets = line.widgets || (line.widgets = []);
      if (widget.insertAt == null) widgets.push(widget);
      else widgets.splice(Math.min(widgets.length - 1, Math.max(0, widget.insertAt)), 0, widget);
      widget.line = line;
      if (cm && !lineIsHidden(doc, line)) {
        var aboveVisible = heightAtLine(line) < doc.scrollTop;
        updateLineHeight(line, line.height + widgetHeight(widget));
        if (aboveVisible) addToScrollPos(cm, null, widget.height);
        cm.curOp.forceUpdate = true;
      }
      return true;
    });
    return widget;
  }

  // LINE DATA STRUCTURE

  // Line objects. These hold state related to a line, including
  // highlighting info (the styles array).
  var Line = CodeMirror.Line = function(text, markedSpans, estimateHeight) {
    this.text = text;
    attachMarkedSpans(this, markedSpans);
    this.height = estimateHeight ? estimateHeight(this) : 1;
  };
  eventMixin(Line);
  Line.prototype.lineNo = function() { return lineNo(this); };

  // Change the content (text, markers) of a line. Automatically
  // invalidates cached information and tries to re-estimate the
  // line's height.
  function updateLine(line, text, markedSpans, estimateHeight) {
    line.text = text;
    if (line.stateAfter) line.stateAfter = null;
    if (line.styles) line.styles = null;
    if (line.order != null) line.order = null;
    detachMarkedSpans(line);
    attachMarkedSpans(line, markedSpans);
    var estHeight = estimateHeight ? estimateHeight(line) : 1;
    if (estHeight != line.height) updateLineHeight(line, estHeight);
  }

  // Detach a line from the document tree and its markers.
  function cleanUpLine(line) {
    line.parent = null;
    detachMarkedSpans(line);
  }

  function extractLineClasses(type, output) {
    if (type) for (;;) {
      var lineClass = type.match(/(?:^|\s+)line-(background-)?(\S+)/);
      if (!lineClass) break;
      type = type.slice(0, lineClass.index) + type.slice(lineClass.index + lineClass[0].length);
      var prop = lineClass[1] ? "bgClass" : "textClass";
      if (output[prop] == null)
        output[prop] = lineClass[2];
      else if (!(new RegExp("(?:^|\s)" + lineClass[2] + "(?:$|\s)")).test(output[prop]))
        output[prop] += " " + lineClass[2];
    }
    return type;
  }

  function callBlankLine(mode, state) {
    if (mode.blankLine) return mode.blankLine(state);
    if (!mode.innerMode) return;
    var inner = CodeMirror.innerMode(mode, state);
    if (inner.mode.blankLine) return inner.mode.blankLine(inner.state);
  }

  function readToken(mode, stream, state, inner) {
    for (var i = 0; i < 10; i++) {
      if (inner) inner[0] = CodeMirror.innerMode(mode, state).mode;
      var style = mode.token(stream, state);
      if (stream.pos > stream.start) return style;
    }
    throw new Error("Mode " + mode.name + " failed to advance stream.");
  }

  // Utility for getTokenAt and getLineTokens
  function takeToken(cm, pos, precise, asArray) {
    function getObj(copy) {
      return {start: stream.start, end: stream.pos,
              string: stream.current(),
              type: style || null,
              state: copy ? copyState(doc.mode, state) : state};
    }

    var doc = cm.doc, mode = doc.mode, style;
    pos = clipPos(doc, pos);
    var line = getLine(doc, pos.line), state = getStateBefore(cm, pos.line, precise);
    var stream = new StringStream(line.text, cm.options.tabSize), tokens;
    if (asArray) tokens = [];
    while ((asArray || stream.pos < pos.ch) && !stream.eol()) {
      stream.start = stream.pos;
      style = readToken(mode, stream, state);
      if (asArray) tokens.push(getObj(true));
    }
    return asArray ? tokens : getObj();
  }

  // Run the given mode's parser over a line, calling f for each token.
  function runMode(cm, text, mode, state, f, lineClasses, forceToEnd) {
    var flattenSpans = mode.flattenSpans;
    if (flattenSpans == null) flattenSpans = cm.options.flattenSpans;
    var curStart = 0, curStyle = null;
    var stream = new StringStream(text, cm.options.tabSize), style;
    var inner = cm.options.addModeClass && [null];
    if (text == "") extractLineClasses(callBlankLine(mode, state), lineClasses);
    while (!stream.eol()) {
      if (stream.pos > cm.options.maxHighlightLength) {
        flattenSpans = false;
        if (forceToEnd) processLine(cm, text, state, stream.pos);
        stream.pos = text.length;
        style = null;
      } else {
        style = extractLineClasses(readToken(mode, stream, state, inner), lineClasses);
      }
      if (inner) {
        var mName = inner[0].name;
        if (mName) style = "m-" + (style ? mName + " " + style : mName);
      }
      if (!flattenSpans || curStyle != style) {
        while (curStart < stream.start) {
          curStart = Math.min(stream.start, curStart + 50000);
          f(curStart, curStyle);
        }
        curStyle = style;
      }
      stream.start = stream.pos;
    }
    while (curStart < stream.pos) {
      // Webkit seems to refuse to render text nodes longer than 57444 characters
      var pos = Math.min(stream.pos, curStart + 50000);
      f(pos, curStyle);
      curStart = pos;
    }
  }

  // Compute a style array (an array starting with a mode generation
  // -- for invalidation -- followed by pairs of end positions and
  // style strings), which is used to highlight the tokens on the
  // line.
  function highlightLine(cm, line, state, forceToEnd) {
    // A styles array always starts with a number identifying the
    // mode/overlays that it is based on (for easy invalidation).
    var st = [cm.state.modeGen], lineClasses = {};
    // Compute the base array of styles
    runMode(cm, line.text, cm.doc.mode, state, function(end, style) {
      st.push(end, style);
    }, lineClasses, forceToEnd);

    // Run overlays, adjust style array.
    for (var o = 0; o < cm.state.overlays.length; ++o) {
      var overlay = cm.state.overlays[o], i = 1, at = 0;
      runMode(cm, line.text, overlay.mode, true, function(end, style) {
        var start = i;
        // Ensure there's a token end at the current position, and that i points at it
        while (at < end) {
          var i_end = st[i];
          if (i_end > end)
            st.splice(i, 1, end, st[i+1], i_end);
          i += 2;
          at = Math.min(end, i_end);
        }
        if (!style) return;
        if (overlay.opaque) {
          st.splice(start, i - start, end, "cm-overlay " + style);
          i = start + 2;
        } else {
          for (; start < i; start += 2) {
            var cur = st[start+1];
            st[start+1] = (cur ? cur + " " : "") + "cm-overlay " + style;
          }
        }
      }, lineClasses);
    }

    return {styles: st, classes: lineClasses.bgClass || lineClasses.textClass ? lineClasses : null};
  }

  function getLineStyles(cm, line, updateFrontier) {
    if (!line.styles || line.styles[0] != cm.state.modeGen) {
      var state = getStateBefore(cm, lineNo(line));
      var result = highlightLine(cm, line, line.text.length > cm.options.maxHighlightLength ? copyState(cm.doc.mode, state) : state);
      line.stateAfter = state;
      line.styles = result.styles;
      if (result.classes) line.styleClasses = result.classes;
      else if (line.styleClasses) line.styleClasses = null;
      if (updateFrontier === cm.doc.frontier) cm.doc.frontier++;
    }
    return line.styles;
  }

  // Lightweight form of highlight -- proceed over this line and
  // update state, but don't save a style array. Used for lines that
  // aren't currently visible.
  function processLine(cm, text, state, startAt) {
    var mode = cm.doc.mode;
    var stream = new StringStream(text, cm.options.tabSize);
    stream.start = stream.pos = startAt || 0;
    if (text == "") callBlankLine(mode, state);
    while (!stream.eol()) {
      readToken(mode, stream, state);
      stream.start = stream.pos;
    }
  }

  // Convert a style as returned by a mode (either null, or a string
  // containing one or more styles) to a CSS style. This is cached,
  // and also looks for line-wide styles.
  var styleToClassCache = {}, styleToClassCacheWithMode = {};
  function interpretTokenStyle(style, options) {
    if (!style || /^\s*$/.test(style)) return null;
    var cache = options.addModeClass ? styleToClassCacheWithMode : styleToClassCache;
    return cache[style] ||
      (cache[style] = style.replace(/\S+/g, "cm-$&"));
  }

  // Render the DOM representation of the text of a line. Also builds
  // up a 'line map', which points at the DOM nodes that represent
  // specific stretches of text, and is used by the measuring code.
  // The returned object contains the DOM node, this map, and
  // information about line-wide styles that were set by the mode.
  function buildLineContent(cm, lineView) {
    // The padding-right forces the element to have a 'border', which
    // is needed on Webkit to be able to get line-level bounding
    // rectangles for it (in measureChar).
    var content = elt("span", null, null, webkit ? "padding-right: .1px" : null);
    var builder = {pre: elt("pre", [content], "CodeMirror-line"), content: content,
                   col: 0, pos: 0, cm: cm,
                   splitSpaces: (ie || webkit) && cm.getOption("lineWrapping")};
    lineView.measure = {};

    // Iterate over the logical lines that make up this visual line.
    for (var i = 0; i <= (lineView.rest ? lineView.rest.length : 0); i++) {
      var line = i ? lineView.rest[i - 1] : lineView.line, order;
      builder.pos = 0;
      builder.addToken = buildToken;
      // Optionally wire in some hacks into the token-rendering
      // algorithm, to deal with browser quirks.
      if (hasBadBidiRects(cm.display.measure) && (order = getOrder(line)))
        builder.addToken = buildTokenBadBidi(builder.addToken, order);
      builder.map = [];
      var allowFrontierUpdate = lineView != cm.display.externalMeasured && lineNo(line);
      insertLineContent(line, builder, getLineStyles(cm, line, allowFrontierUpdate));
      if (line.styleClasses) {
        if (line.styleClasses.bgClass)
          builder.bgClass = joinClasses(line.styleClasses.bgClass, builder.bgClass || "");
        if (line.styleClasses.textClass)
          builder.textClass = joinClasses(line.styleClasses.textClass, builder.textClass || "");
      }

      // Ensure at least a single node is present, for measuring.
      if (builder.map.length == 0)
        builder.map.push(0, 0, builder.content.appendChild(zeroWidthElement(cm.display.measure)));

      // Store the map and a cache object for the current logical line
      if (i == 0) {
        lineView.measure.map = builder.map;
        lineView.measure.cache = {};
      } else {
        (lineView.measure.maps || (lineView.measure.maps = [])).push(builder.map);
        (lineView.measure.caches || (lineView.measure.caches = [])).push({});
      }
    }

    // See issue #2901
    if (webkit) {
      var last = builder.content.lastChild
      if (/\bcm-tab\b/.test(last.className) || (last.querySelector && last.querySelector(".cm-tab")))
        builder.content.className = "cm-tab-wrap-hack";
    }

    signal(cm, "renderLine", cm, lineView.line, builder.pre);
    if (builder.pre.className)
      builder.textClass = joinClasses(builder.pre.className, builder.textClass || "");

    return builder;
  }

  function defaultSpecialCharPlaceholder(ch) {
    var token = elt("span", "\u2022", "cm-invalidchar");
    token.title = "\\u" + ch.charCodeAt(0).toString(16);
    token.setAttribute("aria-label", token.title);
    return token;
  }

  // Build up the DOM representation for a single token, and add it to
  // the line map. Takes care to render special characters separately.
  function buildToken(builder, text, style, startStyle, endStyle, title, css) {
    if (!text) return;
    var displayText = builder.splitSpaces ? text.replace(/ {3,}/g, splitSpaces) : text;
    var special = builder.cm.state.specialChars, mustWrap = false;
    if (!special.test(text)) {
      builder.col += text.length;
      var content = document.createTextNode(displayText);
      builder.map.push(builder.pos, builder.pos + text.length, content);
      if (ie && ie_version < 9) mustWrap = true;
      builder.pos += text.length;
    } else {
      var content = document.createDocumentFragment(), pos = 0;
      while (true) {
        special.lastIndex = pos;
        var m = special.exec(text);
        var skipped = m ? m.index - pos : text.length - pos;
        if (skipped) {
          var txt = document.createTextNode(displayText.slice(pos, pos + skipped));
          if (ie && ie_version < 9) content.appendChild(elt("span", [txt]));
          else content.appendChild(txt);
          builder.map.push(builder.pos, builder.pos + skipped, txt);
          builder.col += skipped;
          builder.pos += skipped;
        }
        if (!m) break;
        pos += skipped + 1;
        if (m[0] == "\t") {
          var tabSize = builder.cm.options.tabSize, tabWidth = tabSize - builder.col % tabSize;
          var txt = content.appendChild(elt("span", spaceStr(tabWidth), "cm-tab"));
          txt.setAttribute("role", "presentation");
          txt.setAttribute("cm-text", "\t");
          builder.col += tabWidth;
        } else if (m[0] == "\r" || m[0] == "\n") {
          var txt = content.appendChild(elt("span", m[0] == "\r" ? "\u240d" : "\u2424", "cm-invalidchar"));
          txt.setAttribute("cm-text", m[0]);
          builder.col += 1;
        } else {
          var txt = builder.cm.options.specialCharPlaceholder(m[0]);
          txt.setAttribute("cm-text", m[0]);
          if (ie && ie_version < 9) content.appendChild(elt("span", [txt]));
          else content.appendChild(txt);
          builder.col += 1;
        }
        builder.map.push(builder.pos, builder.pos + 1, txt);
        builder.pos++;
      }
    }
    if (style || startStyle || endStyle || mustWrap || css) {
      var fullStyle = style || "";
      if (startStyle) fullStyle += startStyle;
      if (endStyle) fullStyle += endStyle;
      var token = elt("span", [content], fullStyle, css);
      if (title) token.title = title;
      return builder.content.appendChild(token);
    }
    builder.content.appendChild(content);
  }

  function splitSpaces(old) {
    var out = " ";
    for (var i = 0; i < old.length - 2; ++i) out += i % 2 ? " " : "\u00a0";
    out += " ";
    return out;
  }

  // Work around nonsense dimensions being reported for stretches of
  // right-to-left text.
  function buildTokenBadBidi(inner, order) {
    return function(builder, text, style, startStyle, endStyle, title, css) {
      style = style ? style + " cm-force-border" : "cm-force-border";
      var start = builder.pos, end = start + text.length;
      for (;;) {
        // Find the part that overlaps with the start of this text
        for (var i = 0; i < order.length; i++) {
          var part = order[i];
          if (part.to > start && part.from <= start) break;
        }
        if (part.to >= end) return inner(builder, text, style, startStyle, endStyle, title, css);
        inner(builder, text.slice(0, part.to - start), style, startStyle, null, title, css);
        startStyle = null;
        text = text.slice(part.to - start);
        start = part.to;
      }
    };
  }

  function buildCollapsedSpan(builder, size, marker, ignoreWidget) {
    var widget = !ignoreWidget && marker.widgetNode;
    if (widget) builder.map.push(builder.pos, builder.pos + size, widget);
    if (!ignoreWidget && builder.cm.display.input.needsContentAttribute) {
      if (!widget)
        widget = builder.content.appendChild(document.createElement("span"));
      widget.setAttribute("cm-marker", marker.id);
    }
    if (widget) {
      builder.cm.display.input.setUneditable(widget);
      builder.content.appendChild(widget);
    }
    builder.pos += size;
  }

  // Outputs a number of spans to make up a line, taking highlighting
  // and marked text into account.
  function insertLineContent(line, builder, styles) {
    var spans = line.markedSpans, allText = line.text, at = 0;
    if (!spans) {
      for (var i = 1; i < styles.length; i+=2)
        builder.addToken(builder, allText.slice(at, at = styles[i]), interpretTokenStyle(styles[i+1], builder.cm.options));
      return;
    }

    var len = allText.length, pos = 0, i = 1, text = "", style, css;
    var nextChange = 0, spanStyle, spanEndStyle, spanStartStyle, title, collapsed;
    for (;;) {
      if (nextChange == pos) { // Update current marker set
        spanStyle = spanEndStyle = spanStartStyle = title = css = "";
        collapsed = null; nextChange = Infinity;
        var foundBookmarks = [], endStyles
        for (var j = 0; j < spans.length; ++j) {
          var sp = spans[j], m = sp.marker;
          if (m.type == "bookmark" && sp.from == pos && m.widgetNode) {
            foundBookmarks.push(m);
          } else if (sp.from <= pos && (sp.to == null || sp.to > pos || m.collapsed && sp.to == pos && sp.from == pos)) {
            if (sp.to != null && sp.to != pos && nextChange > sp.to) {
              nextChange = sp.to;
              spanEndStyle = "";
            }
            if (m.className) spanStyle += " " + m.className;
            if (m.css) css = (css ? css + ";" : "") + m.css;
            if (m.startStyle && sp.from == pos) spanStartStyle += " " + m.startStyle;
            if (m.endStyle && sp.to == nextChange) (endStyles || (endStyles = [])).push(m.endStyle, sp.to)
            if (m.title && !title) title = m.title;
            if (m.collapsed && (!collapsed || compareCollapsedMarkers(collapsed.marker, m) < 0))
              collapsed = sp;
          } else if (sp.from > pos && nextChange > sp.from) {
            nextChange = sp.from;
          }
        }
        if (endStyles) for (var j = 0; j < endStyles.length; j += 2)
          if (endStyles[j + 1] == nextChange) spanEndStyle += " " + endStyles[j]

        if (!collapsed || collapsed.from == pos) for (var j = 0; j < foundBookmarks.length; ++j)
          buildCollapsedSpan(builder, 0, foundBookmarks[j]);
        if (collapsed && (collapsed.from || 0) == pos) {
          buildCollapsedSpan(builder, (collapsed.to == null ? len + 1 : collapsed.to) - pos,
                             collapsed.marker, collapsed.from == null);
          if (collapsed.to == null) return;
          if (collapsed.to == pos) collapsed = false;
        }
      }
      if (pos >= len) break;

      var upto = Math.min(len, nextChange);
      while (true) {
        if (text) {
          var end = pos + text.length;
          if (!collapsed) {
            var tokenText = end > upto ? text.slice(0, upto - pos) : text;
            builder.addToken(builder, tokenText, style ? style + spanStyle : spanStyle,
                             spanStartStyle, pos + tokenText.length == nextChange ? spanEndStyle : "", title, css);
          }
          if (end >= upto) {text = text.slice(upto - pos); pos = upto; break;}
          pos = end;
          spanStartStyle = "";
        }
        text = allText.slice(at, at = styles[i++]);
        style = interpretTokenStyle(styles[i++], builder.cm.options);
      }
    }
  }

  // DOCUMENT DATA STRUCTURE

  // By default, updates that start and end at the beginning of a line
  // are treated specially, in order to make the association of line
  // widgets and marker elements with the text behave more intuitive.
  function isWholeLineUpdate(doc, change) {
    return change.from.ch == 0 && change.to.ch == 0 && lst(change.text) == "" &&
      (!doc.cm || doc.cm.options.wholeLineUpdateBefore);
  }

  // Perform a change on the document data structure.
  function updateDoc(doc, change, markedSpans, estimateHeight) {
    function spansFor(n) {return markedSpans ? markedSpans[n] : null;}
    function update(line, text, spans) {
      updateLine(line, text, spans, estimateHeight);
      signalLater(line, "change", line, change);
    }
    function linesFor(start, end) {
      for (var i = start, result = []; i < end; ++i)
        result.push(new Line(text[i], spansFor(i), estimateHeight));
      return result;
    }

    var from = change.from, to = change.to, text = change.text;
    var firstLine = getLine(doc, from.line), lastLine = getLine(doc, to.line);
    var lastText = lst(text), lastSpans = spansFor(text.length - 1), nlines = to.line - from.line;

    // Adjust the line structure
    if (change.full) {
      doc.insert(0, linesFor(0, text.length));
      doc.remove(text.length, doc.size - text.length);
    } else if (isWholeLineUpdate(doc, change)) {
      // This is a whole-line replace. Treated specially to make
      // sure line objects move the way they are supposed to.
      var added = linesFor(0, text.length - 1);
      update(lastLine, lastLine.text, lastSpans);
      if (nlines) doc.remove(from.line, nlines);
      if (added.length) doc.insert(from.line, added);
    } else if (firstLine == lastLine) {
      if (text.length == 1) {
        update(firstLine, firstLine.text.slice(0, from.ch) + lastText + firstLine.text.slice(to.ch), lastSpans);
      } else {
        var added = linesFor(1, text.length - 1);
        added.push(new Line(lastText + firstLine.text.slice(to.ch), lastSpans, estimateHeight));
        update(firstLine, firstLine.text.slice(0, from.ch) + text[0], spansFor(0));
        doc.insert(from.line + 1, added);
      }
    } else if (text.length == 1) {
      update(firstLine, firstLine.text.slice(0, from.ch) + text[0] + lastLine.text.slice(to.ch), spansFor(0));
      doc.remove(from.line + 1, nlines);
    } else {
      update(firstLine, firstLine.text.slice(0, from.ch) + text[0], spansFor(0));
      update(lastLine, lastText + lastLine.text.slice(to.ch), lastSpans);
      var added = linesFor(1, text.length - 1);
      if (nlines > 1) doc.remove(from.line + 1, nlines - 1);
      doc.insert(from.line + 1, added);
    }

    signalLater(doc, "change", doc, change);
  }

  // The document is represented as a BTree consisting of leaves, with
  // chunk of lines in them, and branches, with up to ten leaves or
  // other branch nodes below them. The top node is always a branch
  // node, and is the document object itself (meaning it has
  // additional methods and properties).
  //
  // All nodes have parent links. The tree is used both to go from
  // line numbers to line objects, and to go from objects to numbers.
  // It also indexes by height, and is used to convert between height
  // and line object, and to find the total height of the document.
  //
  // See also http://marijnhaverbeke.nl/blog/codemirror-line-tree.html

  function LeafChunk(lines) {
    this.lines = lines;
    this.parent = null;
    for (var i = 0, height = 0; i < lines.length; ++i) {
      lines[i].parent = this;
      height += lines[i].height;
    }
    this.height = height;
  }

  LeafChunk.prototype = {
    chunkSize: function() { return this.lines.length; },
    // Remove the n lines at offset 'at'.
    removeInner: function(at, n) {
      for (var i = at, e = at + n; i < e; ++i) {
        var line = this.lines[i];
        this.height -= line.height;
        cleanUpLine(line);
        signalLater(line, "delete");
      }
      this.lines.splice(at, n);
    },
    // Helper used to collapse a small branch into a single leaf.
    collapse: function(lines) {
      lines.push.apply(lines, this.lines);
    },
    // Insert the given array of lines at offset 'at', count them as
    // having the given height.
    insertInner: function(at, lines, height) {
      this.height += height;
      this.lines = this.lines.slice(0, at).concat(lines).concat(this.lines.slice(at));
      for (var i = 0; i < lines.length; ++i) lines[i].parent = this;
    },
    // Used to iterate over a part of the tree.
    iterN: function(at, n, op) {
      for (var e = at + n; at < e; ++at)
        if (op(this.lines[at])) return true;
    }
  };

  function BranchChunk(children) {
    this.children = children;
    var size = 0, height = 0;
    for (var i = 0; i < children.length; ++i) {
      var ch = children[i];
      size += ch.chunkSize(); height += ch.height;
      ch.parent = this;
    }
    this.size = size;
    this.height = height;
    this.parent = null;
  }

  BranchChunk.prototype = {
    chunkSize: function() { return this.size; },
    removeInner: function(at, n) {
      this.size -= n;
      for (var i = 0; i < this.children.length; ++i) {
        var child = this.children[i], sz = child.chunkSize();
        if (at < sz) {
          var rm = Math.min(n, sz - at), oldHeight = child.height;
          child.removeInner(at, rm);
          this.height -= oldHeight - child.height;
          if (sz == rm) { this.children.splice(i--, 1); child.parent = null; }
          if ((n -= rm) == 0) break;
          at = 0;
        } else at -= sz;
      }
      // If the result is smaller than 25 lines, ensure that it is a
      // single leaf node.
      if (this.size - n < 25 &&
          (this.children.length > 1 || !(this.children[0] instanceof LeafChunk))) {
        var lines = [];
        this.collapse(lines);
        this.children = [new LeafChunk(lines)];
        this.children[0].parent = this;
      }
    },
    collapse: function(lines) {
      for (var i = 0; i < this.children.length; ++i) this.children[i].collapse(lines);
    },
    insertInner: function(at, lines, height) {
      this.size += lines.length;
      this.height += height;
      for (var i = 0; i < this.children.length; ++i) {
        var child = this.children[i], sz = child.chunkSize();
        if (at <= sz) {
          child.insertInner(at, lines, height);
          if (child.lines && child.lines.length > 50) {
            // To avoid memory thrashing when child.lines is huge (e.g. first view of a large file), it's never spliced.
            // Instead, small slices are taken. They're taken in order because sequential memory accesses are fastest.
            var remaining = child.lines.length % 25 + 25
            for (var pos = remaining; pos < child.lines.length;) {
              var leaf = new LeafChunk(child.lines.slice(pos, pos += 25));
              child.height -= leaf.height;
              this.children.splice(++i, 0, leaf);
              leaf.parent = this;
            }
            child.lines = child.lines.slice(0, remaining);
            this.maybeSpill();
          }
          break;
        }
        at -= sz;
      }
    },
    // When a node has grown, check whether it should be split.
    maybeSpill: function() {
      if (this.children.length <= 10) return;
      var me = this;
      do {
        var spilled = me.children.splice(me.children.length - 5, 5);
        var sibling = new BranchChunk(spilled);
        if (!me.parent) { // Become the parent node
          var copy = new BranchChunk(me.children);
          copy.parent = me;
          me.children = [copy, sibling];
          me = copy;
       } else {
          me.size -= sibling.size;
          me.height -= sibling.height;
          var myIndex = indexOf(me.parent.children, me);
          me.parent.children.splice(myIndex + 1, 0, sibling);
        }
        sibling.parent = me.parent;
      } while (me.children.length > 10);
      me.parent.maybeSpill();
    },
    iterN: function(at, n, op) {
      for (var i = 0; i < this.children.length; ++i) {
        var child = this.children[i], sz = child.chunkSize();
        if (at < sz) {
          var used = Math.min(n, sz - at);
          if (child.iterN(at, used, op)) return true;
          if ((n -= used) == 0) break;
          at = 0;
        } else at -= sz;
      }
    }
  };

  var nextDocId = 0;
  var Doc = CodeMirror.Doc = function(text, mode, firstLine, lineSep) {
    if (!(this instanceof Doc)) return new Doc(text, mode, firstLine, lineSep);
    if (firstLine == null) firstLine = 0;

    BranchChunk.call(this, [new LeafChunk([new Line("", null)])]);
    this.first = firstLine;
    this.scrollTop = this.scrollLeft = 0;
    this.cantEdit = false;
    this.cleanGeneration = 1;
    this.frontier = firstLine;
    var start = Pos(firstLine, 0);
    this.sel = simpleSelection(start);
    this.history = new History(null);
    this.id = ++nextDocId;
    this.modeOption = mode;
    this.lineSep = lineSep;
    this.extend = false;

    if (typeof text == "string") text = this.splitLines(text);
    updateDoc(this, {from: start, to: start, text: text});
    setSelection(this, simpleSelection(start), sel_dontScroll);
  };

  Doc.prototype = createObj(BranchChunk.prototype, {
    constructor: Doc,
    // Iterate over the document. Supports two forms -- with only one
    // argument, it calls that for each line in the document. With
    // three, it iterates over the range given by the first two (with
    // the second being non-inclusive).
    iter: function(from, to, op) {
      if (op) this.iterN(from - this.first, to - from, op);
      else this.iterN(this.first, this.first + this.size, from);
    },

    // Non-public interface for adding and removing lines.
    insert: function(at, lines) {
      var height = 0;
      for (var i = 0; i < lines.length; ++i) height += lines[i].height;
      this.insertInner(at - this.first, lines, height);
    },
    remove: function(at, n) { this.removeInner(at - this.first, n); },

    // From here, the methods are part of the public interface. Most
    // are also available from CodeMirror (editor) instances.

    getValue: function(lineSep) {
      var lines = getLines(this, this.first, this.first + this.size);
      if (lineSep === false) return lines;
      return lines.join(lineSep || this.lineSeparator());
    },
    setValue: docMethodOp(function(code) {
      var top = Pos(this.first, 0), last = this.first + this.size - 1;
      makeChange(this, {from: top, to: Pos(last, getLine(this, last).text.length),
                        text: this.splitLines(code), origin: "setValue", full: true}, true);
      setSelection(this, simpleSelection(top));
    }),
    replaceRange: function(code, from, to, origin) {
      from = clipPos(this, from);
      to = to ? clipPos(this, to) : from;
      replaceRange(this, code, from, to, origin);
    },
    getRange: function(from, to, lineSep) {
      var lines = getBetween(this, clipPos(this, from), clipPos(this, to));
      if (lineSep === false) return lines;
      return lines.join(lineSep || this.lineSeparator());
    },

    getLine: function(line) {var l = this.getLineHandle(line); return l && l.text;},

    getLineHandle: function(line) {if (isLine(this, line)) return getLine(this, line);},
    getLineNumber: function(line) {return lineNo(line);},

    getLineHandleVisualStart: function(line) {
      if (typeof line == "number") line = getLine(this, line);
      return visualLine(line);
    },

    lineCount: function() {return this.size;},
    firstLine: function() {return this.first;},
    lastLine: function() {return this.first + this.size - 1;},

    clipPos: function(pos) {return clipPos(this, pos);},

    getCursor: function(start) {
      var range = this.sel.primary(), pos;
      if (start == null || start == "head") pos = range.head;
      else if (start == "anchor") pos = range.anchor;
      else if (start == "end" || start == "to" || start === false) pos = range.to();
      else pos = range.from();
      return pos;
    },
    listSelections: function() { return this.sel.ranges; },
    somethingSelected: function() {return this.sel.somethingSelected();},

    setCursor: docMethodOp(function(line, ch, options) {
      setSimpleSelection(this, clipPos(this, typeof line == "number" ? Pos(line, ch || 0) : line), null, options);
    }),
    setSelection: docMethodOp(function(anchor, head, options) {
      setSimpleSelection(this, clipPos(this, anchor), clipPos(this, head || anchor), options);
    }),
    extendSelection: docMethodOp(function(head, other, options) {
      extendSelection(this, clipPos(this, head), other && clipPos(this, other), options);
    }),
    extendSelections: docMethodOp(function(heads, options) {
      extendSelections(this, clipPosArray(this, heads), options);
    }),
    extendSelectionsBy: docMethodOp(function(f, options) {
      var heads = map(this.sel.ranges, f);
      extendSelections(this, clipPosArray(this, heads), options);
    }),
    setSelections: docMethodOp(function(ranges, primary, options) {
      if (!ranges.length) return;
      for (var i = 0, out = []; i < ranges.length; i++)
        out[i] = new Range(clipPos(this, ranges[i].anchor),
                           clipPos(this, ranges[i].head));
      if (primary == null) primary = Math.min(ranges.length - 1, this.sel.primIndex);
      setSelection(this, normalizeSelection(out, primary), options);
    }),
    addSelection: docMethodOp(function(anchor, head, options) {
      var ranges = this.sel.ranges.slice(0);
      ranges.push(new Range(clipPos(this, anchor), clipPos(this, head || anchor)));
      setSelection(this, normalizeSelection(ranges, ranges.length - 1), options);
    }),

    getSelection: function(lineSep) {
      var ranges = this.sel.ranges, lines;
      for (var i = 0; i < ranges.length; i++) {
        var sel = getBetween(this, ranges[i].from(), ranges[i].to());
        lines = lines ? lines.concat(sel) : sel;
      }
      if (lineSep === false) return lines;
      else return lines.join(lineSep || this.lineSeparator());
    },
    getSelections: function(lineSep) {
      var parts = [], ranges = this.sel.ranges;
      for (var i = 0; i < ranges.length; i++) {
        var sel = getBetween(this, ranges[i].from(), ranges[i].to());
        if (lineSep !== false) sel = sel.join(lineSep || this.lineSeparator());
        parts[i] = sel;
      }
      return parts;
    },
    replaceSelection: function(code, collapse, origin) {
      var dup = [];
      for (var i = 0; i < this.sel.ranges.length; i++)
        dup[i] = code;
      this.replaceSelections(dup, collapse, origin || "+input");
    },
    replaceSelections: docMethodOp(function(code, collapse, origin) {
      var changes = [], sel = this.sel;
      for (var i = 0; i < sel.ranges.length; i++) {
        var range = sel.ranges[i];
        changes[i] = {from: range.from(), to: range.to(), text: this.splitLines(code[i]), origin: origin};
      }
      var newSel = collapse && collapse != "end" && computeReplacedSel(this, changes, collapse);
      for (var i = changes.length - 1; i >= 0; i--)
        makeChange(this, changes[i]);
      if (newSel) setSelectionReplaceHistory(this, newSel);
      else if (this.cm) ensureCursorVisible(this.cm);
    }),
    undo: docMethodOp(function() {makeChangeFromHistory(this, "undo");}),
    redo: docMethodOp(function() {makeChangeFromHistory(this, "redo");}),
    undoSelection: docMethodOp(function() {makeChangeFromHistory(this, "undo", true);}),
    redoSelection: docMethodOp(function() {makeChangeFromHistory(this, "redo", true);}),

    setExtending: function(val) {this.extend = val;},
    getExtending: function() {return this.extend;},

    historySize: function() {
      var hist = this.history, done = 0, undone = 0;
      for (var i = 0; i < hist.done.length; i++) if (!hist.done[i].ranges) ++done;
      for (var i = 0; i < hist.undone.length; i++) if (!hist.undone[i].ranges) ++undone;
      return {undo: done, redo: undone};
    },
    clearHistory: function() {this.history = new History(this.history.maxGeneration);},

    markClean: function() {
      this.cleanGeneration = this.changeGeneration(true);
    },
    changeGeneration: function(forceSplit) {
      if (forceSplit)
        this.history.lastOp = this.history.lastSelOp = this.history.lastOrigin = null;
      return this.history.generation;
    },
    isClean: function (gen) {
      return this.history.generation == (gen || this.cleanGeneration);
    },

    getHistory: function() {
      return {done: copyHistoryArray(this.history.done),
              undone: copyHistoryArray(this.history.undone)};
    },
    setHistory: function(histData) {
      var hist = this.history = new History(this.history.maxGeneration);
      hist.done = copyHistoryArray(histData.done.slice(0), null, true);
      hist.undone = copyHistoryArray(histData.undone.slice(0), null, true);
    },

    addLineClass: docMethodOp(function(handle, where, cls) {
      return changeLine(this, handle, where == "gutter" ? "gutter" : "class", function(line) {
        var prop = where == "text" ? "textClass"
                 : where == "background" ? "bgClass"
                 : where == "gutter" ? "gutterClass" : "wrapClass";
        if (!line[prop]) line[prop] = cls;
        else if (classTest(cls).test(line[prop])) return false;
        else line[prop] += " " + cls;
        return true;
      });
    }),
    removeLineClass: docMethodOp(function(handle, where, cls) {
      return changeLine(this, handle, where == "gutter" ? "gutter" : "class", function(line) {
        var prop = where == "text" ? "textClass"
                 : where == "background" ? "bgClass"
                 : where == "gutter" ? "gutterClass" : "wrapClass";
        var cur = line[prop];
        if (!cur) return false;
        else if (cls == null) line[prop] = null;
        else {
          var found = cur.match(classTest(cls));
          if (!found) return false;
          var end = found.index + found[0].length;
          line[prop] = cur.slice(0, found.index) + (!found.index || end == cur.length ? "" : " ") + cur.slice(end) || null;
        }
        return true;
      });
    }),

    addLineWidget: docMethodOp(function(handle, node, options) {
      return addLineWidget(this, handle, node, options);
    }),
    removeLineWidget: function(widget) { widget.clear(); },

    markText: function(from, to, options) {
      return markText(this, clipPos(this, from), clipPos(this, to), options, options && options.type || "range");
    },
    setBookmark: function(pos, options) {
      var realOpts = {replacedWith: options && (options.nodeType == null ? options.widget : options),
                      insertLeft: options && options.insertLeft,
                      clearWhenEmpty: false, shared: options && options.shared,
                      handleMouseEvents: options && options.handleMouseEvents};
      pos = clipPos(this, pos);
      return markText(this, pos, pos, realOpts, "bookmark");
    },
    findMarksAt: function(pos) {
      pos = clipPos(this, pos);
      var markers = [], spans = getLine(this, pos.line).markedSpans;
      if (spans) for (var i = 0; i < spans.length; ++i) {
        var span = spans[i];
        if ((span.from == null || span.from <= pos.ch) &&
            (span.to == null || span.to >= pos.ch))
          markers.push(span.marker.parent || span.marker);
      }
      return markers;
    },
    findMarks: function(from, to, filter) {
      from = clipPos(this, from); to = clipPos(this, to);
      var found = [], lineNo = from.line;
      this.iter(from.line, to.line + 1, function(line) {
        var spans = line.markedSpans;
        if (spans) for (var i = 0; i < spans.length; i++) {
          var span = spans[i];
          if (!(span.to != null && lineNo == from.line && from.ch >= span.to ||
                span.from == null && lineNo != from.line ||
                span.from != null && lineNo == to.line && span.from >= to.ch) &&
              (!filter || filter(span.marker)))
            found.push(span.marker.parent || span.marker);
        }
        ++lineNo;
      });
      return found;
    },
    getAllMarks: function() {
      var markers = [];
      this.iter(function(line) {
        var sps = line.markedSpans;
        if (sps) for (var i = 0; i < sps.length; ++i)
          if (sps[i].from != null) markers.push(sps[i].marker);
      });
      return markers;
    },

    posFromIndex: function(off) {
      var ch, lineNo = this.first, sepSize = this.lineSeparator().length;
      this.iter(function(line) {
        var sz = line.text.length + sepSize;
        if (sz > off) { ch = off; return true; }
        off -= sz;
        ++lineNo;
      });
      return clipPos(this, Pos(lineNo, ch));
    },
    indexFromPos: function (coords) {
      coords = clipPos(this, coords);
      var index = coords.ch;
      if (coords.line < this.first || coords.ch < 0) return 0;
      var sepSize = this.lineSeparator().length;
      this.iter(this.first, coords.line, function (line) {
        index += line.text.length + sepSize;
      });
      return index;
    },

    copy: function(copyHistory) {
      var doc = new Doc(getLines(this, this.first, this.first + this.size),
                        this.modeOption, this.first, this.lineSep);
      doc.scrollTop = this.scrollTop; doc.scrollLeft = this.scrollLeft;
      doc.sel = this.sel;
      doc.extend = false;
      if (copyHistory) {
        doc.history.undoDepth = this.history.undoDepth;
        doc.setHistory(this.getHistory());
      }
      return doc;
    },

    linkedDoc: function(options) {
      if (!options) options = {};
      var from = this.first, to = this.first + this.size;
      if (options.from != null && options.from > from) from = options.from;
      if (options.to != null && options.to < to) to = options.to;
      var copy = new Doc(getLines(this, from, to), options.mode || this.modeOption, from, this.lineSep);
      if (options.sharedHist) copy.history = this.history;
      (this.linked || (this.linked = [])).push({doc: copy, sharedHist: options.sharedHist});
      copy.linked = [{doc: this, isParent: true, sharedHist: options.sharedHist}];
      copySharedMarkers(copy, findSharedMarkers(this));
      return copy;
    },
    unlinkDoc: function(other) {
      if (other instanceof CodeMirror) other = other.doc;
      if (this.linked) for (var i = 0; i < this.linked.length; ++i) {
        var link = this.linked[i];
        if (link.doc != other) continue;
        this.linked.splice(i, 1);
        other.unlinkDoc(this);
        detachSharedMarkers(findSharedMarkers(this));
        break;
      }
      // If the histories were shared, split them again
      if (other.history == this.history) {
        var splitIds = [other.id];
        linkedDocs(other, function(doc) {splitIds.push(doc.id);}, true);
        other.history = new History(null);
        other.history.done = copyHistoryArray(this.history.done, splitIds);
        other.history.undone = copyHistoryArray(this.history.undone, splitIds);
      }
    },
    iterLinkedDocs: function(f) {linkedDocs(this, f);},

    getMode: function() {return this.mode;},
    getEditor: function() {return this.cm;},

    splitLines: function(str) {
      if (this.lineSep) return str.split(this.lineSep);
      return splitLinesAuto(str);
    },
    lineSeparator: function() { return this.lineSep || "\n"; }
  });

  // Public alias.
  Doc.prototype.eachLine = Doc.prototype.iter;

  // Set up methods on CodeMirror's prototype to redirect to the editor's document.
  var dontDelegate = "iter insert remove copy getEditor constructor".split(" ");
  for (var prop in Doc.prototype) if (Doc.prototype.hasOwnProperty(prop) && indexOf(dontDelegate, prop) < 0)
    CodeMirror.prototype[prop] = (function(method) {
      return function() {return method.apply(this.doc, arguments);};
    })(Doc.prototype[prop]);

  eventMixin(Doc);

  // Call f for all linked documents.
  function linkedDocs(doc, f, sharedHistOnly) {
    function propagate(doc, skip, sharedHist) {
      if (doc.linked) for (var i = 0; i < doc.linked.length; ++i) {
        var rel = doc.linked[i];
        if (rel.doc == skip) continue;
        var shared = sharedHist && rel.sharedHist;
        if (sharedHistOnly && !shared) continue;
        f(rel.doc, shared);
        propagate(rel.doc, doc, shared);
      }
    }
    propagate(doc, null, true);
  }

  // Attach a document to an editor.
  function attachDoc(cm, doc) {
    if (doc.cm) throw new Error("This document is already in use.");
    cm.doc = doc;
    doc.cm = cm;
    estimateLineHeights(cm);
    loadMode(cm);
    if (!cm.options.lineWrapping) findMaxLine(cm);
    cm.options.mode = doc.modeOption;
    regChange(cm);
  }

  // LINE UTILITIES

  // Find the line object corresponding to the given line number.
  function getLine(doc, n) {
    n -= doc.first;
    if (n < 0 || n >= doc.size) throw new Error("There is no line " + (n + doc.first) + " in the document.");
    for (var chunk = doc; !chunk.lines;) {
      for (var i = 0;; ++i) {
        var child = chunk.children[i], sz = child.chunkSize();
        if (n < sz) { chunk = child; break; }
        n -= sz;
      }
    }
    return chunk.lines[n];
  }

  // Get the part of a document between two positions, as an array of
  // strings.
  function getBetween(doc, start, end) {
    var out = [], n = start.line;
    doc.iter(start.line, end.line + 1, function(line) {
      var text = line.text;
      if (n == end.line) text = text.slice(0, end.ch);
      if (n == start.line) text = text.slice(start.ch);
      out.push(text);
      ++n;
    });
    return out;
  }
  // Get the lines between from and to, as array of strings.
  function getLines(doc, from, to) {
    var out = [];
    doc.iter(from, to, function(line) { out.push(line.text); });
    return out;
  }

  // Update the height of a line, propagating the height change
  // upwards to parent nodes.
  function updateLineHeight(line, height) {
    var diff = height - line.height;
    if (diff) for (var n = line; n; n = n.parent) n.height += diff;
  }

  // Given a line object, find its line number by walking up through
  // its parent links.
  function lineNo(line) {
    if (line.parent == null) return null;
    var cur = line.parent, no = indexOf(cur.lines, line);
    for (var chunk = cur.parent; chunk; cur = chunk, chunk = chunk.parent) {
      for (var i = 0;; ++i) {
        if (chunk.children[i] == cur) break;
        no += chunk.children[i].chunkSize();
      }
    }
    return no + cur.first;
  }

  // Find the line at the given vertical position, using the height
  // information in the document tree.
  function lineAtHeight(chunk, h) {
    var n = chunk.first;
    outer: do {
      for (var i = 0; i < chunk.children.length; ++i) {
        var child = chunk.children[i], ch = child.height;
        if (h < ch) { chunk = child; continue outer; }
        h -= ch;
        n += child.chunkSize();
      }
      return n;
    } while (!chunk.lines);
    for (var i = 0; i < chunk.lines.length; ++i) {
      var line = chunk.lines[i], lh = line.height;
      if (h < lh) break;
      h -= lh;
    }
    return n + i;
  }


  // Find the height above the given line.
  function heightAtLine(lineObj) {
    lineObj = visualLine(lineObj);

    var h = 0, chunk = lineObj.parent;
    for (var i = 0; i < chunk.lines.length; ++i) {
      var line = chunk.lines[i];
      if (line == lineObj) break;
      else h += line.height;
    }
    for (var p = chunk.parent; p; chunk = p, p = chunk.parent) {
      for (var i = 0; i < p.children.length; ++i) {
        var cur = p.children[i];
        if (cur == chunk) break;
        else h += cur.height;
      }
    }
    return h;
  }

  // Get the bidi ordering for the given line (and cache it). Returns
  // false for lines that are fully left-to-right, and an array of
  // BidiSpan objects otherwise.
  function getOrder(line) {
    var order = line.order;
    if (order == null) order = line.order = bidiOrdering(line.text);
    return order;
  }

  // HISTORY

  function History(startGen) {
    // Arrays of change events and selections. Doing something adds an
    // event to done and clears undo. Undoing moves events from done
    // to undone, redoing moves them in the other direction.
    this.done = []; this.undone = [];
    this.undoDepth = Infinity;
    // Used to track when changes can be merged into a single undo
    // event
    this.lastModTime = this.lastSelTime = 0;
    this.lastOp = this.lastSelOp = null;
    this.lastOrigin = this.lastSelOrigin = null;
    // Used by the isClean() method
    this.generation = this.maxGeneration = startGen || 1;
  }

  // Create a history change event from an updateDoc-style change
  // object.
  function historyChangeFromChange(doc, change) {
    var histChange = {from: copyPos(change.from), to: changeEnd(change), text: getBetween(doc, change.from, change.to)};
    attachLocalSpans(doc, histChange, change.from.line, change.to.line + 1);
    linkedDocs(doc, function(doc) {attachLocalSpans(doc, histChange, change.from.line, change.to.line + 1);}, true);
    return histChange;
  }

  // Pop all selection events off the end of a history array. Stop at
  // a change event.
  function clearSelectionEvents(array) {
    while (array.length) {
      var last = lst(array);
      if (last.ranges) array.pop();
      else break;
    }
  }

  // Find the top change event in the history. Pop off selection
  // events that are in the way.
  function lastChangeEvent(hist, force) {
    if (force) {
      clearSelectionEvents(hist.done);
      return lst(hist.done);
    } else if (hist.done.length && !lst(hist.done).ranges) {
      return lst(hist.done);
    } else if (hist.done.length > 1 && !hist.done[hist.done.length - 2].ranges) {
      hist.done.pop();
      return lst(hist.done);
    }
  }

  // Register a change in the history. Merges changes that are within
  // a single operation, ore are close together with an origin that
  // allows merging (starting with "+") into a single event.
  function addChangeToHistory(doc, change, selAfter, opId) {
    var hist = doc.history;
    hist.undone.length = 0;
    var time = +new Date, cur;

    if ((hist.lastOp == opId ||
         hist.lastOrigin == change.origin && change.origin &&
         ((change.origin.charAt(0) == "+" && doc.cm && hist.lastModTime > time - doc.cm.options.historyEventDelay) ||
          change.origin.charAt(0) == "*")) &&
        (cur = lastChangeEvent(hist, hist.lastOp == opId))) {
      // Merge this change into the last event
      var last = lst(cur.changes);
      if (cmp(change.from, change.to) == 0 && cmp(change.from, last.to) == 0) {
        // Optimized case for simple insertion -- don't want to add
        // new changesets for every character typed
        last.to = changeEnd(change);
      } else {
        // Add new sub-event
        cur.changes.push(historyChangeFromChange(doc, change));
      }
    } else {
      // Can not be merged, start a new event.
      var before = lst(hist.done);
      if (!before || !before.ranges)
        pushSelectionToHistory(doc.sel, hist.done);
      cur = {changes: [historyChangeFromChange(doc, change)],
             generation: hist.generation};
      hist.done.push(cur);
      while (hist.done.length > hist.undoDepth) {
        hist.done.shift();
        if (!hist.done[0].ranges) hist.done.shift();
      }
    }
    hist.done.push(selAfter);
    hist.generation = ++hist.maxGeneration;
    hist.lastModTime = hist.lastSelTime = time;
    hist.lastOp = hist.lastSelOp = opId;
    hist.lastOrigin = hist.lastSelOrigin = change.origin;

    if (!last) signal(doc, "historyAdded");
  }

  function selectionEventCanBeMerged(doc, origin, prev, sel) {
    var ch = origin.charAt(0);
    return ch == "*" ||
      ch == "+" &&
      prev.ranges.length == sel.ranges.length &&
      prev.somethingSelected() == sel.somethingSelected() &&
      new Date - doc.history.lastSelTime <= (doc.cm ? doc.cm.options.historyEventDelay : 500);
  }

  // Called whenever the selection changes, sets the new selection as
  // the pending selection in the history, and pushes the old pending
  // selection into the 'done' array when it was significantly
  // different (in number of selected ranges, emptiness, or time).
  function addSelectionToHistory(doc, sel, opId, options) {
    var hist = doc.history, origin = options && options.origin;

    // A new event is started when the previous origin does not match
    // the current, or the origins don't allow matching. Origins
    // starting with * are always merged, those starting with + are
    // merged when similar and close together in time.
    if (opId == hist.lastSelOp ||
        (origin && hist.lastSelOrigin == origin &&
         (hist.lastModTime == hist.lastSelTime && hist.lastOrigin == origin ||
          selectionEventCanBeMerged(doc, origin, lst(hist.done), sel))))
      hist.done[hist.done.length - 1] = sel;
    else
      pushSelectionToHistory(sel, hist.done);

    hist.lastSelTime = +new Date;
    hist.lastSelOrigin = origin;
    hist.lastSelOp = opId;
    if (options && options.clearRedo !== false)
      clearSelectionEvents(hist.undone);
  }

  function pushSelectionToHistory(sel, dest) {
    var top = lst(dest);
    if (!(top && top.ranges && top.equals(sel)))
      dest.push(sel);
  }

  // Used to store marked span information in the history.
  function attachLocalSpans(doc, change, from, to) {
    var existing = change["spans_" + doc.id], n = 0;
    doc.iter(Math.max(doc.first, from), Math.min(doc.first + doc.size, to), function(line) {
      if (line.markedSpans)
        (existing || (existing = change["spans_" + doc.id] = {}))[n] = line.markedSpans;
      ++n;
    });
  }

  // When un/re-doing restores text containing marked spans, those
  // that have been explicitly cleared should not be restored.
  function removeClearedSpans(spans) {
    if (!spans) return null;
    for (var i = 0, out; i < spans.length; ++i) {
      if (spans[i].marker.explicitlyCleared) { if (!out) out = spans.slice(0, i); }
      else if (out) out.push(spans[i]);
    }
    return !out ? spans : out.length ? out : null;
  }

  // Retrieve and filter the old marked spans stored in a change event.
  function getOldSpans(doc, change) {
    var found = change["spans_" + doc.id];
    if (!found) return null;
    for (var i = 0, nw = []; i < change.text.length; ++i)
      nw.push(removeClearedSpans(found[i]));
    return nw;
  }

  // Used both to provide a JSON-safe object in .getHistory, and, when
  // detaching a document, to split the history in two
  function copyHistoryArray(events, newGroup, instantiateSel) {
    for (var i = 0, copy = []; i < events.length; ++i) {
      var event = events[i];
      if (event.ranges) {
        copy.push(instantiateSel ? Selection.prototype.deepCopy.call(event) : event);
        continue;
      }
      var changes = event.changes, newChanges = [];
      copy.push({changes: newChanges});
      for (var j = 0; j < changes.length; ++j) {
        var change = changes[j], m;
        newChanges.push({from: change.from, to: change.to, text: change.text});
        if (newGroup) for (var prop in change) if (m = prop.match(/^spans_(\d+)$/)) {
          if (indexOf(newGroup, Number(m[1])) > -1) {
            lst(newChanges)[prop] = change[prop];
            delete change[prop];
          }
        }
      }
    }
    return copy;
  }

  // Rebasing/resetting history to deal with externally-sourced changes

  function rebaseHistSelSingle(pos, from, to, diff) {
    if (to < pos.line) {
      pos.line += diff;
    } else if (from < pos.line) {
      pos.line = from;
      pos.ch = 0;
    }
  }

  // Tries to rebase an array of history events given a change in the
  // document. If the change touches the same lines as the event, the
  // event, and everything 'behind' it, is discarded. If the change is
  // before the event, the event's positions are updated. Uses a
  // copy-on-write scheme for the positions, to avoid having to
  // reallocate them all on every rebase, but also avoid problems with
  // shared position objects being unsafely updated.
  function rebaseHistArray(array, from, to, diff) {
    for (var i = 0; i < array.length; ++i) {
      var sub = array[i], ok = true;
      if (sub.ranges) {
        if (!sub.copied) { sub = array[i] = sub.deepCopy(); sub.copied = true; }
        for (var j = 0; j < sub.ranges.length; j++) {
          rebaseHistSelSingle(sub.ranges[j].anchor, from, to, diff);
          rebaseHistSelSingle(sub.ranges[j].head, from, to, diff);
        }
        continue;
      }
      for (var j = 0; j < sub.changes.length; ++j) {
        var cur = sub.changes[j];
        if (to < cur.from.line) {
          cur.from = Pos(cur.from.line + diff, cur.from.ch);
          cur.to = Pos(cur.to.line + diff, cur.to.ch);
        } else if (from <= cur.to.line) {
          ok = false;
          break;
        }
      }
      if (!ok) {
        array.splice(0, i + 1);
        i = 0;
      }
    }
  }

  function rebaseHist(hist, change) {
    var from = change.from.line, to = change.to.line, diff = change.text.length - (to - from) - 1;
    rebaseHistArray(hist.done, from, to, diff);
    rebaseHistArray(hist.undone, from, to, diff);
  }

  // EVENT UTILITIES

  // Due to the fact that we still support jurassic IE versions, some
  // compatibility wrappers are needed.

  var e_preventDefault = CodeMirror.e_preventDefault = function(e) {
    if (e.preventDefault) e.preventDefault();
    else e.returnValue = false;
  };
  var e_stopPropagation = CodeMirror.e_stopPropagation = function(e) {
    if (e.stopPropagation) e.stopPropagation();
    else e.cancelBubble = true;
  };
  function e_defaultPrevented(e) {
    return e.defaultPrevented != null ? e.defaultPrevented : e.returnValue == false;
  }
  var e_stop = CodeMirror.e_stop = function(e) {e_preventDefault(e); e_stopPropagation(e);};

  function e_target(e) {return e.target || e.srcElement;}
  function e_button(e) {
    var b = e.which;
    if (b == null) {
      if (e.button & 1) b = 1;
      else if (e.button & 2) b = 3;
      else if (e.button & 4) b = 2;
    }
    if (mac && e.ctrlKey && b == 1) b = 3;
    return b;
  }

  // EVENT HANDLING

  // Lightweight event framework. on/off also work on DOM nodes,
  // registering native DOM handlers.

  var on = CodeMirror.on = function(emitter, type, f) {
    if (emitter.addEventListener)
      emitter.addEventListener(type, f, false);
    else if (emitter.attachEvent)
      emitter.attachEvent("on" + type, f);
    else {
      var map = emitter._handlers || (emitter._handlers = {});
      var arr = map[type] || (map[type] = []);
      arr.push(f);
    }
  };

  var noHandlers = []
  function getHandlers(emitter, type, copy) {
    var arr = emitter._handlers && emitter._handlers[type]
    if (copy) return arr && arr.length > 0 ? arr.slice() : noHandlers
    else return arr || noHandlers
  }

  var off = CodeMirror.off = function(emitter, type, f) {
    if (emitter.removeEventListener)
      emitter.removeEventListener(type, f, false);
    else if (emitter.detachEvent)
      emitter.detachEvent("on" + type, f);
    else {
      var handlers = getHandlers(emitter, type, false)
      for (var i = 0; i < handlers.length; ++i)
        if (handlers[i] == f) { handlers.splice(i, 1); break; }
    }
  };

  var signal = CodeMirror.signal = function(emitter, type /*, values...*/) {
    var handlers = getHandlers(emitter, type, true)
    if (!handlers.length) return;
    var args = Array.prototype.slice.call(arguments, 2);
    for (var i = 0; i < handlers.length; ++i) handlers[i].apply(null, args);
  };

  var orphanDelayedCallbacks = null;

  // Often, we want to signal events at a point where we are in the
  // middle of some work, but don't want the handler to start calling
  // other methods on the editor, which might be in an inconsistent
  // state or simply not expect any other events to happen.
  // signalLater looks whether there are any handlers, and schedules
  // them to be executed when the last operation ends, or, if no
  // operation is active, when a timeout fires.
  function signalLater(emitter, type /*, values...*/) {
    var arr = getHandlers(emitter, type, false)
    if (!arr.length) return;
    var args = Array.prototype.slice.call(arguments, 2), list;
    if (operationGroup) {
      list = operationGroup.delayedCallbacks;
    } else if (orphanDelayedCallbacks) {
      list = orphanDelayedCallbacks;
    } else {
      list = orphanDelayedCallbacks = [];
      setTimeout(fireOrphanDelayed, 0);
    }
    function bnd(f) {return function(){f.apply(null, args);};};
    for (var i = 0; i < arr.length; ++i)
      list.push(bnd(arr[i]));
  }

  function fireOrphanDelayed() {
    var delayed = orphanDelayedCallbacks;
    orphanDelayedCallbacks = null;
    for (var i = 0; i < delayed.length; ++i) delayed[i]();
  }

  // The DOM events that CodeMirror handles can be overridden by
  // registering a (non-DOM) handler on the editor for the event name,
  // and preventDefault-ing the event in that handler.
  function signalDOMEvent(cm, e, override) {
    if (typeof e == "string")
      e = {type: e, preventDefault: function() { this.defaultPrevented = true; }};
    signal(cm, override || e.type, cm, e);
    return e_defaultPrevented(e) || e.codemirrorIgnore;
  }

  function signalCursorActivity(cm) {
    var arr = cm._handlers && cm._handlers.cursorActivity;
    if (!arr) return;
    var set = cm.curOp.cursorActivityHandlers || (cm.curOp.cursorActivityHandlers = []);
    for (var i = 0; i < arr.length; ++i) if (indexOf(set, arr[i]) == -1)
      set.push(arr[i]);
  }

  function hasHandler(emitter, type) {
    return getHandlers(emitter, type).length > 0
  }

  // Add on and off methods to a constructor's prototype, to make
  // registering events on such objects more convenient.
  function eventMixin(ctor) {
    ctor.prototype.on = function(type, f) {on(this, type, f);};
    ctor.prototype.off = function(type, f) {off(this, type, f);};
  }

  // MISC UTILITIES

  // Number of pixels added to scroller and sizer to hide scrollbar
  var scrollerGap = 30;

  // Returned or thrown by various protocols to signal 'I'm not
  // handling this'.
  var Pass = CodeMirror.Pass = {toString: function(){return "CodeMirror.Pass";}};

  // Reused option objects for setSelection & friends
  var sel_dontScroll = {scroll: false}, sel_mouse = {origin: "*mouse"}, sel_move = {origin: "+move"};

  function Delayed() {this.id = null;}
  Delayed.prototype.set = function(ms, f) {
    clearTimeout(this.id);
    this.id = setTimeout(f, ms);
  };

  // Counts the column offset in a string, taking tabs into account.
  // Used mostly to find indentation.
  var countColumn = CodeMirror.countColumn = function(string, end, tabSize, startIndex, startValue) {
    if (end == null) {
      end = string.search(/[^\s\u00a0]/);
      if (end == -1) end = string.length;
    }
    for (var i = startIndex || 0, n = startValue || 0;;) {
      var nextTab = string.indexOf("\t", i);
      if (nextTab < 0 || nextTab >= end)
        return n + (end - i);
      n += nextTab - i;
      n += tabSize - (n % tabSize);
      i = nextTab + 1;
    }
  };

  // The inverse of countColumn -- find the offset that corresponds to
  // a particular column.
  var findColumn = CodeMirror.findColumn = function(string, goal, tabSize) {
    for (var pos = 0, col = 0;;) {
      var nextTab = string.indexOf("\t", pos);
      if (nextTab == -1) nextTab = string.length;
      var skipped = nextTab - pos;
      if (nextTab == string.length || col + skipped >= goal)
        return pos + Math.min(skipped, goal - col);
      col += nextTab - pos;
      col += tabSize - (col % tabSize);
      pos = nextTab + 1;
      if (col >= goal) return pos;
    }
  }

  var spaceStrs = [""];
  function spaceStr(n) {
    while (spaceStrs.length <= n)
      spaceStrs.push(lst(spaceStrs) + " ");
    return spaceStrs[n];
  }

  function lst(arr) { return arr[arr.length-1]; }

  var selectInput = function(node) { node.select(); };
  if (ios) // Mobile Safari apparently has a bug where select() is broken.
    selectInput = function(node) { node.selectionStart = 0; node.selectionEnd = node.value.length; };
  else if (ie) // Suppress mysterious IE10 errors
    selectInput = function(node) { try { node.select(); } catch(_e) {} };

  function indexOf(array, elt) {
    for (var i = 0; i < array.length; ++i)
      if (array[i] == elt) return i;
    return -1;
  }
  function map(array, f) {
    var out = [];
    for (var i = 0; i < array.length; i++) out[i] = f(array[i], i);
    return out;
  }

  function nothing() {}

  function createObj(base, props) {
    var inst;
    if (Object.create) {
      inst = Object.create(base);
    } else {
      nothing.prototype = base;
      inst = new nothing();
    }
    if (props) copyObj(props, inst);
    return inst;
  };

  function copyObj(obj, target, overwrite) {
    if (!target) target = {};
    for (var prop in obj)
      if (obj.hasOwnProperty(prop) && (overwrite !== false || !target.hasOwnProperty(prop)))
        target[prop] = obj[prop];
    return target;
  }

  function bind(f) {
    var args = Array.prototype.slice.call(arguments, 1);
    return function(){return f.apply(null, args);};
  }

  var nonASCIISingleCaseWordChar = /[\u00df\u0587\u0590-\u05f4\u0600-\u06ff\u3040-\u309f\u30a0-\u30ff\u3400-\u4db5\u4e00-\u9fcc\uac00-\ud7af]/;
  var isWordCharBasic = CodeMirror.isWordChar = function(ch) {
    return /\w/.test(ch) || ch > "\x80" &&
      (ch.toUpperCase() != ch.toLowerCase() || nonASCIISingleCaseWordChar.test(ch));
  };
  function isWordChar(ch, helper) {
    if (!helper) return isWordCharBasic(ch);
    if (helper.source.indexOf("\\w") > -1 && isWordCharBasic(ch)) return true;
    return helper.test(ch);
  }

  function isEmpty(obj) {
    for (var n in obj) if (obj.hasOwnProperty(n) && obj[n]) return false;
    return true;
  }

  // Extending unicode characters. A series of a non-extending char +
  // any number of extending chars is treated as a single unit as far
  // as editing and measuring is concerned. This is not fully correct,
  // since some scripts/fonts/browsers also treat other configurations
  // of code points as a group.
  var extendingChars = /[\u0300-\u036f\u0483-\u0489\u0591-\u05bd\u05bf\u05c1\u05c2\u05c4\u05c5\u05c7\u0610-\u061a\u064b-\u065e\u0670\u06d6-\u06dc\u06de-\u06e4\u06e7\u06e8\u06ea-\u06ed\u0711\u0730-\u074a\u07a6-\u07b0\u07eb-\u07f3\u0816-\u0819\u081b-\u0823\u0825-\u0827\u0829-\u082d\u0900-\u0902\u093c\u0941-\u0948\u094d\u0951-\u0955\u0962\u0963\u0981\u09bc\u09be\u09c1-\u09c4\u09cd\u09d7\u09e2\u09e3\u0a01\u0a02\u0a3c\u0a41\u0a42\u0a47\u0a48\u0a4b-\u0a4d\u0a51\u0a70\u0a71\u0a75\u0a81\u0a82\u0abc\u0ac1-\u0ac5\u0ac7\u0ac8\u0acd\u0ae2\u0ae3\u0b01\u0b3c\u0b3e\u0b3f\u0b41-\u0b44\u0b4d\u0b56\u0b57\u0b62\u0b63\u0b82\u0bbe\u0bc0\u0bcd\u0bd7\u0c3e-\u0c40\u0c46-\u0c48\u0c4a-\u0c4d\u0c55\u0c56\u0c62\u0c63\u0cbc\u0cbf\u0cc2\u0cc6\u0ccc\u0ccd\u0cd5\u0cd6\u0ce2\u0ce3\u0d3e\u0d41-\u0d44\u0d4d\u0d57\u0d62\u0d63\u0dca\u0dcf\u0dd2-\u0dd4\u0dd6\u0ddf\u0e31\u0e34-\u0e3a\u0e47-\u0e4e\u0eb1\u0eb4-\u0eb9\u0ebb\u0ebc\u0ec8-\u0ecd\u0f18\u0f19\u0f35\u0f37\u0f39\u0f71-\u0f7e\u0f80-\u0f84\u0f86\u0f87\u0f90-\u0f97\u0f99-\u0fbc\u0fc6\u102d-\u1030\u1032-\u1037\u1039\u103a\u103d\u103e\u1058\u1059\u105e-\u1060\u1071-\u1074\u1082\u1085\u1086\u108d\u109d\u135f\u1712-\u1714\u1732-\u1734\u1752\u1753\u1772\u1773\u17b7-\u17bd\u17c6\u17c9-\u17d3\u17dd\u180b-\u180d\u18a9\u1920-\u1922\u1927\u1928\u1932\u1939-\u193b\u1a17\u1a18\u1a56\u1a58-\u1a5e\u1a60\u1a62\u1a65-\u1a6c\u1a73-\u1a7c\u1a7f\u1b00-\u1b03\u1b34\u1b36-\u1b3a\u1b3c\u1b42\u1b6b-\u1b73\u1b80\u1b81\u1ba2-\u1ba5\u1ba8\u1ba9\u1c2c-\u1c33\u1c36\u1c37\u1cd0-\u1cd2\u1cd4-\u1ce0\u1ce2-\u1ce8\u1ced\u1dc0-\u1de6\u1dfd-\u1dff\u200c\u200d\u20d0-\u20f0\u2cef-\u2cf1\u2de0-\u2dff\u302a-\u302f\u3099\u309a\ua66f-\ua672\ua67c\ua67d\ua6f0\ua6f1\ua802\ua806\ua80b\ua825\ua826\ua8c4\ua8e0-\ua8f1\ua926-\ua92d\ua947-\ua951\ua980-\ua982\ua9b3\ua9b6-\ua9b9\ua9bc\uaa29-\uaa2e\uaa31\uaa32\uaa35\uaa36\uaa43\uaa4c\uaab0\uaab2-\uaab4\uaab7\uaab8\uaabe\uaabf\uaac1\uabe5\uabe8\uabed\udc00-\udfff\ufb1e\ufe00-\ufe0f\ufe20-\ufe26\uff9e\uff9f]/;
  function isExtendingChar(ch) { return ch.charCodeAt(0) >= 768 && extendingChars.test(ch); }

  // DOM UTILITIES

  function elt(tag, content, className, style) {
    var e = document.createElement(tag);
    if (className) e.className = className;
    if (style) e.style.cssText = style;
    if (typeof content == "string") e.appendChild(document.createTextNode(content));
    else if (content) for (var i = 0; i < content.length; ++i) e.appendChild(content[i]);
    return e;
  }

  var range;
  if (document.createRange) range = function(node, start, end, endNode) {
    var r = document.createRange();
    r.setEnd(endNode || node, end);
    r.setStart(node, start);
    return r;
  };
  else range = function(node, start, end) {
    var r = document.body.createTextRange();
    try { r.moveToElementText(node.parentNode); }
    catch(e) { return r; }
    r.collapse(true);
    r.moveEnd("character", end);
    r.moveStart("character", start);
    return r;
  };

  function removeChildren(e) {
    for (var count = e.childNodes.length; count > 0; --count)
      e.removeChild(e.firstChild);
    return e;
  }

  function removeChildrenAndAdd(parent, e) {
    return removeChildren(parent).appendChild(e);
  }

  var contains = CodeMirror.contains = function(parent, child) {
    if (child.nodeType == 3) // Android browser always returns false when child is a textnode
      child = child.parentNode;
    if (parent.contains)
      return parent.contains(child);
    do {
      if (child.nodeType == 11) child = child.host;
      if (child == parent) return true;
    } while (child = child.parentNode);
  };

  function activeElt() {
    var activeElement = document.activeElement;
    while (activeElement && activeElement.root && activeElement.root.activeElement)
      activeElement = activeElement.root.activeElement;
    return activeElement;
  }
  // Older versions of IE throws unspecified error when touching
  // document.activeElement in some cases (during loading, in iframe)
  if (ie && ie_version < 11) activeElt = function() {
    try { return document.activeElement; }
    catch(e) { return document.body; }
  };

  function classTest(cls) { return new RegExp("(^|\\s)" + cls + "(?:$|\\s)\\s*"); }
  var rmClass = CodeMirror.rmClass = function(node, cls) {
    var current = node.className;
    var match = classTest(cls).exec(current);
    if (match) {
      var after = current.slice(match.index + match[0].length);
      node.className = current.slice(0, match.index) + (after ? match[1] + after : "");
    }
  };
  var addClass = CodeMirror.addClass = function(node, cls) {
    var current = node.className;
    if (!classTest(cls).test(current)) node.className += (current ? " " : "") + cls;
  };
  function joinClasses(a, b) {
    var as = a.split(" ");
    for (var i = 0; i < as.length; i++)
      if (as[i] && !classTest(as[i]).test(b)) b += " " + as[i];
    return b;
  }

  // WINDOW-WIDE EVENTS

  // These must be handled carefully, because naively registering a
  // handler for each editor will cause the editors to never be
  // garbage collected.

  function forEachCodeMirror(f) {
    if (!document.body.getElementsByClassName) return;
    var byClass = document.body.getElementsByClassName("CodeMirror");
    for (var i = 0; i < byClass.length; i++) {
      var cm = byClass[i].CodeMirror;
      if (cm) f(cm);
    }
  }

  var globalsRegistered = false;
  function ensureGlobalHandlers() {
    if (globalsRegistered) return;
    registerGlobalHandlers();
    globalsRegistered = true;
  }
  function registerGlobalHandlers() {
    // When the window resizes, we need to refresh active editors.
    var resizeTimer;
    on(window, "resize", function() {
      if (resizeTimer == null) resizeTimer = setTimeout(function() {
        resizeTimer = null;
        forEachCodeMirror(onResize);
      }, 100);
    });
    // When the window loses focus, we want to show the editor as blurred
    on(window, "blur", function() {
      forEachCodeMirror(onBlur);
    });
  }

  // FEATURE DETECTION

  // Detect drag-and-drop
  var dragAndDrop = function() {
    // There is *some* kind of drag-and-drop support in IE6-8, but I
    // couldn't get it to work yet.
    if (ie && ie_version < 9) return false;
    var div = elt('div');
    return "draggable" in div || "dragDrop" in div;
  }();

  var zwspSupported;
  function zeroWidthElement(measure) {
    if (zwspSupported == null) {
      var test = elt("span", "\u200b");
      removeChildrenAndAdd(measure, elt("span", [test, document.createTextNode("x")]));
      if (measure.firstChild.offsetHeight != 0)
        zwspSupported = test.offsetWidth <= 1 && test.offsetHeight > 2 && !(ie && ie_version < 8);
    }
    var node = zwspSupported ? elt("span", "\u200b") :
      elt("span", "\u00a0", null, "display: inline-block; width: 1px; margin-right: -1px");
    node.setAttribute("cm-text", "");
    return node;
  }

  // Feature-detect IE's crummy client rect reporting for bidi text
  var badBidiRects;
  function hasBadBidiRects(measure) {
    if (badBidiRects != null) return badBidiRects;
    var txt = removeChildrenAndAdd(measure, document.createTextNode("A\u062eA"));
    var r0 = range(txt, 0, 1).getBoundingClientRect();
    if (!r0 || r0.left == r0.right) return false; // Safari returns null in some cases (#2780)
    var r1 = range(txt, 1, 2).getBoundingClientRect();
    return badBidiRects = (r1.right - r0.right < 3);
  }

  // See if "".split is the broken IE version, if so, provide an
  // alternative way to split lines.
  var splitLinesAuto = CodeMirror.splitLines = "\n\nb".split(/\n/).length != 3 ? function(string) {
    var pos = 0, result = [], l = string.length;
    while (pos <= l) {
      var nl = string.indexOf("\n", pos);
      if (nl == -1) nl = string.length;
      var line = string.slice(pos, string.charAt(nl - 1) == "\r" ? nl - 1 : nl);
      var rt = line.indexOf("\r");
      if (rt != -1) {
        result.push(line.slice(0, rt));
        pos += rt + 1;
      } else {
        result.push(line);
        pos = nl + 1;
      }
    }
    return result;
  } : function(string){return string.split(/\r\n?|\n/);};

  var hasSelection = window.getSelection ? function(te) {
    try { return te.selectionStart != te.selectionEnd; }
    catch(e) { return false; }
  } : function(te) {
    try {var range = te.ownerDocument.selection.createRange();}
    catch(e) {}
    if (!range || range.parentElement() != te) return false;
    return range.compareEndPoints("StartToEnd", range) != 0;
  };

  var hasCopyEvent = (function() {
    var e = elt("div");
    if ("oncopy" in e) return true;
    e.setAttribute("oncopy", "return;");
    return typeof e.oncopy == "function";
  })();

  var badZoomedRects = null;
  function hasBadZoomedRects(measure) {
    if (badZoomedRects != null) return badZoomedRects;
    var node = removeChildrenAndAdd(measure, elt("span", "x"));
    var normal = node.getBoundingClientRect();
    var fromRange = range(node, 0, 1).getBoundingClientRect();
    return badZoomedRects = Math.abs(normal.left - fromRange.left) > 1;
  }

  // KEY NAMES

  var keyNames = CodeMirror.keyNames = {
    3: "Enter", 8: "Backspace", 9: "Tab", 13: "Enter", 16: "Shift", 17: "Ctrl", 18: "Alt",
    19: "Pause", 20: "CapsLock", 27: "Esc", 32: "Space", 33: "PageUp", 34: "PageDown", 35: "End",
    36: "Home", 37: "Left", 38: "Up", 39: "Right", 40: "Down", 44: "PrintScrn", 45: "Insert",
    46: "Delete", 59: ";", 61: "=", 91: "Mod", 92: "Mod", 93: "Mod",
    106: "*", 107: "=", 109: "-", 110: ".", 111: "/", 127: "Delete",
    173: "-", 186: ";", 187: "=", 188: ",", 189: "-", 190: ".", 191: "/", 192: "`", 219: "[", 220: "\\",
    221: "]", 222: "'", 63232: "Up", 63233: "Down", 63234: "Left", 63235: "Right", 63272: "Delete",
    63273: "Home", 63275: "End", 63276: "PageUp", 63277: "PageDown", 63302: "Insert"
  };
  (function() {
    // Number keys
    for (var i = 0; i < 10; i++) keyNames[i + 48] = keyNames[i + 96] = String(i);
    // Alphabetic keys
    for (var i = 65; i <= 90; i++) keyNames[i] = String.fromCharCode(i);
    // Function keys
    for (var i = 1; i <= 12; i++) keyNames[i + 111] = keyNames[i + 63235] = "F" + i;
  })();

  // BIDI HELPERS

  function iterateBidiSections(order, from, to, f) {
    if (!order) return f(from, to, "ltr");
    var found = false;
    for (var i = 0; i < order.length; ++i) {
      var part = order[i];
      if (part.from < to && part.to > from || from == to && part.to == from) {
        f(Math.max(part.from, from), Math.min(part.to, to), part.level == 1 ? "rtl" : "ltr");
        found = true;
      }
    }
    if (!found) f(from, to, "ltr");
  }

  function bidiLeft(part) { return part.level % 2 ? part.to : part.from; }
  function bidiRight(part) { return part.level % 2 ? part.from : part.to; }

  function lineLeft(line) { var order = getOrder(line); return order ? bidiLeft(order[0]) : 0; }
  function lineRight(line) {
    var order = getOrder(line);
    if (!order) return line.text.length;
    return bidiRight(lst(order));
  }

  function lineStart(cm, lineN) {
    var line = getLine(cm.doc, lineN);
    var visual = visualLine(line);
    if (visual != line) lineN = lineNo(visual);
    var order = getOrder(visual);
    var ch = !order ? 0 : order[0].level % 2 ? lineRight(visual) : lineLeft(visual);
    return Pos(lineN, ch);
  }
  function lineEnd(cm, lineN) {
    var merged, line = getLine(cm.doc, lineN);
    while (merged = collapsedSpanAtEnd(line)) {
      line = merged.find(1, true).line;
      lineN = null;
    }
    var order = getOrder(line);
    var ch = !order ? line.text.length : order[0].level % 2 ? lineLeft(line) : lineRight(line);
    return Pos(lineN == null ? lineNo(line) : lineN, ch);
  }
  function lineStartSmart(cm, pos) {
    var start = lineStart(cm, pos.line);
    var line = getLine(cm.doc, start.line);
    var order = getOrder(line);
    if (!order || order[0].level == 0) {
      var firstNonWS = Math.max(0, line.text.search(/\S/));
      var inWS = pos.line == start.line && pos.ch <= firstNonWS && pos.ch;
      return Pos(start.line, inWS ? 0 : firstNonWS);
    }
    return start;
  }

  function compareBidiLevel(order, a, b) {
    var linedir = order[0].level;
    if (a == linedir) return true;
    if (b == linedir) return false;
    return a < b;
  }
  var bidiOther;
  function getBidiPartAt(order, pos) {
    bidiOther = null;
    for (var i = 0, found; i < order.length; ++i) {
      var cur = order[i];
      if (cur.from < pos && cur.to > pos) return i;
      if ((cur.from == pos || cur.to == pos)) {
        if (found == null) {
          found = i;
        } else if (compareBidiLevel(order, cur.level, order[found].level)) {
          if (cur.from != cur.to) bidiOther = found;
          return i;
        } else {
          if (cur.from != cur.to) bidiOther = i;
          return found;
        }
      }
    }
    return found;
  }

  function moveInLine(line, pos, dir, byUnit) {
    if (!byUnit) return pos + dir;
    do pos += dir;
    while (pos > 0 && isExtendingChar(line.text.charAt(pos)));
    return pos;
  }

  // This is needed in order to move 'visually' through bi-directional
  // text -- i.e., pressing left should make the cursor go left, even
  // when in RTL text. The tricky part is the 'jumps', where RTL and
  // LTR text touch each other. This often requires the cursor offset
  // to move more than one unit, in order to visually move one unit.
  function moveVisually(line, start, dir, byUnit) {
    var bidi = getOrder(line);
    if (!bidi) return moveLogically(line, start, dir, byUnit);
    var pos = getBidiPartAt(bidi, start), part = bidi[pos];
    var target = moveInLine(line, start, part.level % 2 ? -dir : dir, byUnit);

    for (;;) {
      if (target > part.from && target < part.to) return target;
      if (target == part.from || target == part.to) {
        if (getBidiPartAt(bidi, target) == pos) return target;
        part = bidi[pos += dir];
        return (dir > 0) == part.level % 2 ? part.to : part.from;
      } else {
        part = bidi[pos += dir];
        if (!part) return null;
        if ((dir > 0) == part.level % 2)
          target = moveInLine(line, part.to, -1, byUnit);
        else
          target = moveInLine(line, part.from, 1, byUnit);
      }
    }
  }

  function moveLogically(line, start, dir, byUnit) {
    var target = start + dir;
    if (byUnit) while (target > 0 && isExtendingChar(line.text.charAt(target))) target += dir;
    return target < 0 || target > line.text.length ? null : target;
  }

  // Bidirectional ordering algorithm
  // See http://unicode.org/reports/tr9/tr9-13.html for the algorithm
  // that this (partially) implements.

  // One-char codes used for character types:
  // L (L):   Left-to-Right
  // R (R):   Right-to-Left
  // r (AL):  Right-to-Left Arabic
  // 1 (EN):  European Number
  // + (ES):  European Number Separator
  // % (ET):  European Number Terminator
  // n (AN):  Arabic Number
  // , (CS):  Common Number Separator
  // m (NSM): Non-Spacing Mark
  // b (BN):  Boundary Neutral
  // s (B):   Paragraph Separator
  // t (S):   Segment Separator
  // w (WS):  Whitespace
  // N (ON):  Other Neutrals

  // Returns null if characters are ordered as they appear
  // (left-to-right), or an array of sections ({from, to, level}
  // objects) in the order in which they occur visually.
  var bidiOrdering = (function() {
    // Character types for codepoints 0 to 0xff
    var lowTypes = "bbbbbbbbbtstwsbbbbbbbbbbbbbbssstwNN%%%NNNNNN,N,N1111111111NNNNNNNLLLLLLLLLLLLLLLLLLLLLLLLLLNNNNNNLLLLLLLLLLLLLLLLLLLLLLLLLLNNNNbbbbbbsbbbbbbbbbbbbbbbbbbbbbbbbbb,N%%%%NNNNLNNNNN%%11NLNNN1LNNNNNLLLLLLLLLLLLLLLLLLLLLLLNLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLN";
    // Character types for codepoints 0x600 to 0x6ff
    var arabicTypes = "rrrrrrrrrrrr,rNNmmmmmmrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrmmmmmmmmmmmmmmrrrrrrrnnnnnnnnnn%nnrrrmrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrmmmmmmmmmmmmmmmmmmmNmmmm";
    function charType(code) {
      if (code <= 0xf7) return lowTypes.charAt(code);
      else if (0x590 <= code && code <= 0x5f4) return "R";
      else if (0x600 <= code && code <= 0x6ed) return arabicTypes.charAt(code - 0x600);
      else if (0x6ee <= code && code <= 0x8ac) return "r";
      else if (0x2000 <= code && code <= 0x200b) return "w";
      else if (code == 0x200c) return "b";
      else return "L";
    }

    var bidiRE = /[\u0590-\u05f4\u0600-\u06ff\u0700-\u08ac]/;
    var isNeutral = /[stwN]/, isStrong = /[LRr]/, countsAsLeft = /[Lb1n]/, countsAsNum = /[1n]/;
    // Browsers seem to always treat the boundaries of block elements as being L.
    var outerType = "L";

    function BidiSpan(level, from, to) {
      this.level = level;
      this.from = from; this.to = to;
    }

    return function(str) {
      if (!bidiRE.test(str)) return false;
      var len = str.length, types = [];
      for (var i = 0, type; i < len; ++i)
        types.push(type = charType(str.charCodeAt(i)));

      // W1. Examine each non-spacing mark (NSM) in the level run, and
      // change the type of the NSM to the type of the previous
      // character. If the NSM is at the start of the level run, it will
      // get the type of sor.
      for (var i = 0, prev = outerType; i < len; ++i) {
        var type = types[i];
        if (type == "m") types[i] = prev;
        else prev = type;
      }

      // W2. Search backwards from each instance of a European number
      // until the first strong type (R, L, AL, or sor) is found. If an
      // AL is found, change the type of the European number to Arabic
      // number.
      // W3. Change all ALs to R.
      for (var i = 0, cur = outerType; i < len; ++i) {
        var type = types[i];
        if (type == "1" && cur == "r") types[i] = "n";
        else if (isStrong.test(type)) { cur = type; if (type == "r") types[i] = "R"; }
      }

      // W4. A single European separator between two European numbers
      // changes to a European number. A single common separator between
      // two numbers of the same type changes to that type.
      for (var i = 1, prev = types[0]; i < len - 1; ++i) {
        var type = types[i];
        if (type == "+" && prev == "1" && types[i+1] == "1") types[i] = "1";
        else if (type == "," && prev == types[i+1] &&
                 (prev == "1" || prev == "n")) types[i] = prev;
        prev = type;
      }

      // W5. A sequence of European terminators adjacent to European
      // numbers changes to all European numbers.
      // W6. Otherwise, separators and terminators change to Other
      // Neutral.
      for (var i = 0; i < len; ++i) {
        var type = types[i];
        if (type == ",") types[i] = "N";
        else if (type == "%") {
          for (var end = i + 1; end < len && types[end] == "%"; ++end) {}
          var replace = (i && types[i-1] == "!") || (end < len && types[end] == "1") ? "1" : "N";
          for (var j = i; j < end; ++j) types[j] = replace;
          i = end - 1;
        }
      }

      // W7. Search backwards from each instance of a European number
      // until the first strong type (R, L, or sor) is found. If an L is
      // found, then change the type of the European number to L.
      for (var i = 0, cur = outerType; i < len; ++i) {
        var type = types[i];
        if (cur == "L" && type == "1") types[i] = "L";
        else if (isStrong.test(type)) cur = type;
      }

      // N1. A sequence of neutrals takes the direction of the
      // surrounding strong text if the text on both sides has the same
      // direction. European and Arabic numbers act as if they were R in
      // terms of their influence on neutrals. Start-of-level-run (sor)
      // and end-of-level-run (eor) are used at level run boundaries.
      // N2. Any remaining neutrals take the embedding direction.
      for (var i = 0; i < len; ++i) {
        if (isNeutral.test(types[i])) {
          for (var end = i + 1; end < len && isNeutral.test(types[end]); ++end) {}
          var before = (i ? types[i-1] : outerType) == "L";
          var after = (end < len ? types[end] : outerType) == "L";
          var replace = before || after ? "L" : "R";
          for (var j = i; j < end; ++j) types[j] = replace;
          i = end - 1;
        }
      }

      // Here we depart from the documented algorithm, in order to avoid
      // building up an actual levels array. Since there are only three
      // levels (0, 1, 2) in an implementation that doesn't take
      // explicit embedding into account, we can build up the order on
      // the fly, without following the level-based algorithm.
      var order = [], m;
      for (var i = 0; i < len;) {
        if (countsAsLeft.test(types[i])) {
          var start = i;
          for (++i; i < len && countsAsLeft.test(types[i]); ++i) {}
          order.push(new BidiSpan(0, start, i));
        } else {
          var pos = i, at = order.length;
          for (++i; i < len && types[i] != "L"; ++i) {}
          for (var j = pos; j < i;) {
            if (countsAsNum.test(types[j])) {
              if (pos < j) order.splice(at, 0, new BidiSpan(1, pos, j));
              var nstart = j;
              for (++j; j < i && countsAsNum.test(types[j]); ++j) {}
              order.splice(at, 0, new BidiSpan(2, nstart, j));
              pos = j;
            } else ++j;
          }
          if (pos < i) order.splice(at, 0, new BidiSpan(1, pos, i));
        }
      }
      if (order[0].level == 1 && (m = str.match(/^\s+/))) {
        order[0].from = m[0].length;
        order.unshift(new BidiSpan(0, 0, m[0].length));
      }
      if (lst(order).level == 1 && (m = str.match(/\s+$/))) {
        lst(order).to -= m[0].length;
        order.push(new BidiSpan(0, len - m[0].length, len));
      }
      if (order[0].level == 2)
        order.unshift(new BidiSpan(1, order[0].to, order[0].to));
      if (order[0].level != lst(order).level)
        order.push(new BidiSpan(order[0].level, len, len));

      return order;
    };
  })();

  // THE END

  CodeMirror.version = "5.16.0";

  return CodeMirror;
});
(function() {
  jQuery(function() {
    $("a[rel~=popover], .has-popover").popover();
    return $("a[rel~=tooltip], .has-tooltip").tooltip();
  });

}).call(this);
(function() {
  (function() {
    (function() {
      var slice = [].slice;

      this.ActionCable = {
        INTERNAL: {
          "message_types": {
            "welcome": "welcome",
            "ping": "ping",
            "confirmation": "confirm_subscription",
            "rejection": "reject_subscription"
          },
          "default_mount_path": "/cable",
          "protocols": ["actioncable-v1-json", "actioncable-unsupported"]
        },
        createConsumer: function(url) {
          var ref;
          if (url == null) {
            url = (ref = this.getConfig("url")) != null ? ref : this.INTERNAL.default_mount_path;
          }
          return new ActionCable.Consumer(this.createWebSocketURL(url));
        },
        getConfig: function(name) {
          var element;
          element = document.head.querySelector("meta[name='action-cable-" + name + "']");
          return element != null ? element.getAttribute("content") : void 0;
        },
        createWebSocketURL: function(url) {
          var a;
          if (url && !/^wss?:/i.test(url)) {
            a = document.createElement("a");
            a.href = url;
            a.href = a.href;
            a.protocol = a.protocol.replace("http", "ws");
            return a.href;
          } else {
            return url;
          }
        },
        startDebugging: function() {
          return this.debugging = true;
        },
        stopDebugging: function() {
          return this.debugging = null;
        },
        log: function() {
          var messages;
          messages = 1 <= arguments.length ? slice.call(arguments, 0) : [];
          if (this.debugging) {
            messages.push(Date.now());
            return console.log.apply(console, ["[ActionCable]"].concat(slice.call(messages)));
          }
        }
      };

    }).call(this);
  }).call(this);

  var ActionCable = this.ActionCable;

  (function() {
    (function() {
      var bind = function(fn, me){ return function(){ return fn.apply(me, arguments); }; };

      ActionCable.ConnectionMonitor = (function() {
        var clamp, now, secondsSince;

        ConnectionMonitor.pollInterval = {
          min: 3,
          max: 30
        };

        ConnectionMonitor.staleThreshold = 6;

        function ConnectionMonitor(connection) {
          this.connection = connection;
          this.visibilityDidChange = bind(this.visibilityDidChange, this);
          this.reconnectAttempts = 0;
        }

        ConnectionMonitor.prototype.start = function() {
          if (!this.isRunning()) {
            this.startedAt = now();
            delete this.stoppedAt;
            this.startPolling();
            document.addEventListener("visibilitychange", this.visibilityDidChange);
            return ActionCable.log("ConnectionMonitor started. pollInterval = " + (this.getPollInterval()) + " ms");
          }
        };

        ConnectionMonitor.prototype.stop = function() {
          if (this.isRunning()) {
            this.stoppedAt = now();
            this.stopPolling();
            document.removeEventListener("visibilitychange", this.visibilityDidChange);
            return ActionCable.log("ConnectionMonitor stopped");
          }
        };

        ConnectionMonitor.prototype.isRunning = function() {
          return (this.startedAt != null) && (this.stoppedAt == null);
        };

        ConnectionMonitor.prototype.recordPing = function() {
          return this.pingedAt = now();
        };

        ConnectionMonitor.prototype.recordConnect = function() {
          this.reconnectAttempts = 0;
          this.recordPing();
          delete this.disconnectedAt;
          return ActionCable.log("ConnectionMonitor recorded connect");
        };

        ConnectionMonitor.prototype.recordDisconnect = function() {
          this.disconnectedAt = now();
          return ActionCable.log("ConnectionMonitor recorded disconnect");
        };

        ConnectionMonitor.prototype.startPolling = function() {
          this.stopPolling();
          return this.poll();
        };

        ConnectionMonitor.prototype.stopPolling = function() {
          return clearTimeout(this.pollTimeout);
        };

        ConnectionMonitor.prototype.poll = function() {
          return this.pollTimeout = setTimeout((function(_this) {
            return function() {
              _this.reconnectIfStale();
              return _this.poll();
            };
          })(this), this.getPollInterval());
        };

        ConnectionMonitor.prototype.getPollInterval = function() {
          var interval, max, min, ref;
          ref = this.constructor.pollInterval, min = ref.min, max = ref.max;
          interval = 5 * Math.log(this.reconnectAttempts + 1);
          return Math.round(clamp(interval, min, max) * 1000);
        };

        ConnectionMonitor.prototype.reconnectIfStale = function() {
          if (this.connectionIsStale()) {
            ActionCable.log("ConnectionMonitor detected stale connection. reconnectAttempts = " + this.reconnectAttempts + ", pollInterval = " + (this.getPollInterval()) + " ms, time disconnected = " + (secondsSince(this.disconnectedAt)) + " s, stale threshold = " + this.constructor.staleThreshold + " s");
            this.reconnectAttempts++;
            if (this.disconnectedRecently()) {
              return ActionCable.log("ConnectionMonitor skipping reopening recent disconnect");
            } else {
              ActionCable.log("ConnectionMonitor reopening");
              return this.connection.reopen();
            }
          }
        };

        ConnectionMonitor.prototype.connectionIsStale = function() {
          var ref;
          return secondsSince((ref = this.pingedAt) != null ? ref : this.startedAt) > this.constructor.staleThreshold;
        };

        ConnectionMonitor.prototype.disconnectedRecently = function() {
          return this.disconnectedAt && secondsSince(this.disconnectedAt) < this.constructor.staleThreshold;
        };

        ConnectionMonitor.prototype.visibilityDidChange = function() {
          if (document.visibilityState === "visible") {
            return setTimeout((function(_this) {
              return function() {
                if (_this.connectionIsStale() || !_this.connection.isOpen()) {
                  ActionCable.log("ConnectionMonitor reopening stale connection on visibilitychange. visbilityState = " + document.visibilityState);
                  return _this.connection.reopen();
                }
              };
            })(this), 200);
          }
        };

        now = function() {
          return new Date().getTime();
        };

        secondsSince = function(time) {
          return (now() - time) / 1000;
        };

        clamp = function(number, min, max) {
          return Math.max(min, Math.min(max, number));
        };

        return ConnectionMonitor;

      })();

    }).call(this);
    (function() {
      var i, message_types, protocols, ref, supportedProtocols, unsupportedProtocol,
        slice = [].slice,
        bind = function(fn, me){ return function(){ return fn.apply(me, arguments); }; },
        indexOf = [].indexOf || function(item) { for (var i = 0, l = this.length; i < l; i++) { if (i in this && this[i] === item) return i; } return -1; };

      ref = ActionCable.INTERNAL, message_types = ref.message_types, protocols = ref.protocols;

      supportedProtocols = 2 <= protocols.length ? slice.call(protocols, 0, i = protocols.length - 1) : (i = 0, []), unsupportedProtocol = protocols[i++];

      ActionCable.Connection = (function() {
        Connection.reopenDelay = 500;

        function Connection(consumer) {
          this.consumer = consumer;
          this.open = bind(this.open, this);
          this.subscriptions = this.consumer.subscriptions;
          this.monitor = new ActionCable.ConnectionMonitor(this);
          this.disconnected = true;
        }

        Connection.prototype.send = function(data) {
          if (this.isOpen()) {
            this.webSocket.send(JSON.stringify(data));
            return true;
          } else {
            return false;
          }
        };

        Connection.prototype.open = function() {
          if (this.isActive()) {
            ActionCable.log("Attempted to open WebSocket, but existing socket is " + (this.getState()));
            throw new Error("Existing connection must be closed before opening");
          } else {
            ActionCable.log("Opening WebSocket, current state is " + (this.getState()) + ", subprotocols: " + protocols);
            if (this.webSocket != null) {
              this.uninstallEventHandlers();
            }
            this.webSocket = new WebSocket(this.consumer.url, protocols);
            this.installEventHandlers();
            this.monitor.start();
            return true;
          }
        };

        Connection.prototype.close = function(arg) {
          var allowReconnect, ref1;
          allowReconnect = (arg != null ? arg : {
            allowReconnect: true
          }).allowReconnect;
          if (!allowReconnect) {
            this.monitor.stop();
          }
          if (this.isActive()) {
            return (ref1 = this.webSocket) != null ? ref1.close() : void 0;
          }
        };

        Connection.prototype.reopen = function() {
          var error;
          ActionCable.log("Reopening WebSocket, current state is " + (this.getState()));
          if (this.isActive()) {
            try {
              return this.close();
            } catch (error1) {
              error = error1;
              return ActionCable.log("Failed to reopen WebSocket", error);
            } finally {
              ActionCable.log("Reopening WebSocket in " + this.constructor.reopenDelay + "ms");
              setTimeout(this.open, this.constructor.reopenDelay);
            }
          } else {
            return this.open();
          }
        };

        Connection.prototype.getProtocol = function() {
          var ref1;
          return (ref1 = this.webSocket) != null ? ref1.protocol : void 0;
        };

        Connection.prototype.isOpen = function() {
          return this.isState("open");
        };

        Connection.prototype.isActive = function() {
          return this.isState("open", "connecting");
        };

        Connection.prototype.isProtocolSupported = function() {
          var ref1;
          return ref1 = this.getProtocol(), indexOf.call(supportedProtocols, ref1) >= 0;
        };

        Connection.prototype.isState = function() {
          var ref1, states;
          states = 1 <= arguments.length ? slice.call(arguments, 0) : [];
          return ref1 = this.getState(), indexOf.call(states, ref1) >= 0;
        };

        Connection.prototype.getState = function() {
          var ref1, state, value;
          for (state in WebSocket) {
            value = WebSocket[state];
            if (value === ((ref1 = this.webSocket) != null ? ref1.readyState : void 0)) {
              return state.toLowerCase();
            }
          }
          return null;
        };

        Connection.prototype.installEventHandlers = function() {
          var eventName, handler;
          for (eventName in this.events) {
            handler = this.events[eventName].bind(this);
            this.webSocket["on" + eventName] = handler;
          }
        };

        Connection.prototype.uninstallEventHandlers = function() {
          var eventName;
          for (eventName in this.events) {
            this.webSocket["on" + eventName] = function() {};
          }
        };

        Connection.prototype.events = {
          message: function(event) {
            var identifier, message, ref1, type;
            if (!this.isProtocolSupported()) {
              return;
            }
            ref1 = JSON.parse(event.data), identifier = ref1.identifier, message = ref1.message, type = ref1.type;
            switch (type) {
              case message_types.welcome:
                this.monitor.recordConnect();
                return this.subscriptions.reload();
              case message_types.ping:
                return this.monitor.recordPing();
              case message_types.confirmation:
                return this.subscriptions.notify(identifier, "connected");
              case message_types.rejection:
                return this.subscriptions.reject(identifier);
              default:
                return this.subscriptions.notify(identifier, "received", message);
            }
          },
          open: function() {
            ActionCable.log("WebSocket onopen event, using '" + (this.getProtocol()) + "' subprotocol");
            this.disconnected = false;
            if (!this.isProtocolSupported()) {
              ActionCable.log("Protocol is unsupported. Stopping monitor and disconnecting.");
              return this.close({
                allowReconnect: false
              });
            }
          },
          close: function(event) {
            ActionCable.log("WebSocket onclose event");
            if (this.disconnected) {
              return;
            }
            this.disconnected = true;
            this.monitor.recordDisconnect();
            return this.subscriptions.notifyAll("disconnected", {
              willAttemptReconnect: this.monitor.isRunning()
            });
          },
          error: function() {
            return ActionCable.log("WebSocket onerror event");
          }
        };

        return Connection;

      })();

    }).call(this);
    (function() {
      var slice = [].slice;

      ActionCable.Subscriptions = (function() {
        function Subscriptions(consumer) {
          this.consumer = consumer;
          this.subscriptions = [];
        }

        Subscriptions.prototype.create = function(channelName, mixin) {
          var channel, params, subscription;
          channel = channelName;
          params = typeof channel === "object" ? channel : {
            channel: channel
          };
          subscription = new ActionCable.Subscription(this.consumer, params, mixin);
          return this.add(subscription);
        };

        Subscriptions.prototype.add = function(subscription) {
          this.subscriptions.push(subscription);
          this.consumer.ensureActiveConnection();
          this.notify(subscription, "initialized");
          this.sendCommand(subscription, "subscribe");
          return subscription;
        };

        Subscriptions.prototype.remove = function(subscription) {
          this.forget(subscription);
          if (!this.findAll(subscription.identifier).length) {
            this.sendCommand(subscription, "unsubscribe");
          }
          return subscription;
        };

        Subscriptions.prototype.reject = function(identifier) {
          var i, len, ref, results, subscription;
          ref = this.findAll(identifier);
          results = [];
          for (i = 0, len = ref.length; i < len; i++) {
            subscription = ref[i];
            this.forget(subscription);
            this.notify(subscription, "rejected");
            results.push(subscription);
          }
          return results;
        };

        Subscriptions.prototype.forget = function(subscription) {
          var s;
          this.subscriptions = (function() {
            var i, len, ref, results;
            ref = this.subscriptions;
            results = [];
            for (i = 0, len = ref.length; i < len; i++) {
              s = ref[i];
              if (s !== subscription) {
                results.push(s);
              }
            }
            return results;
          }).call(this);
          return subscription;
        };

        Subscriptions.prototype.findAll = function(identifier) {
          var i, len, ref, results, s;
          ref = this.subscriptions;
          results = [];
          for (i = 0, len = ref.length; i < len; i++) {
            s = ref[i];
            if (s.identifier === identifier) {
              results.push(s);
            }
          }
          return results;
        };

        Subscriptions.prototype.reload = function() {
          var i, len, ref, results, subscription;
          ref = this.subscriptions;
          results = [];
          for (i = 0, len = ref.length; i < len; i++) {
            subscription = ref[i];
            results.push(this.sendCommand(subscription, "subscribe"));
          }
          return results;
        };

        Subscriptions.prototype.notifyAll = function() {
          var args, callbackName, i, len, ref, results, subscription;
          callbackName = arguments[0], args = 2 <= arguments.length ? slice.call(arguments, 1) : [];
          ref = this.subscriptions;
          results = [];
          for (i = 0, len = ref.length; i < len; i++) {
            subscription = ref[i];
            results.push(this.notify.apply(this, [subscription, callbackName].concat(slice.call(args))));
          }
          return results;
        };

        Subscriptions.prototype.notify = function() {
          var args, callbackName, i, len, results, subscription, subscriptions;
          subscription = arguments[0], callbackName = arguments[1], args = 3 <= arguments.length ? slice.call(arguments, 2) : [];
          if (typeof subscription === "string") {
            subscriptions = this.findAll(subscription);
          } else {
            subscriptions = [subscription];
          }
          results = [];
          for (i = 0, len = subscriptions.length; i < len; i++) {
            subscription = subscriptions[i];
            results.push(typeof subscription[callbackName] === "function" ? subscription[callbackName].apply(subscription, args) : void 0);
          }
          return results;
        };

        Subscriptions.prototype.sendCommand = function(subscription, command) {
          var identifier;
          identifier = subscription.identifier;
          return this.consumer.send({
            command: command,
            identifier: identifier
          });
        };

        return Subscriptions;

      })();

    }).call(this);
    (function() {
      ActionCable.Subscription = (function() {
        var extend;

        function Subscription(consumer, params, mixin) {
          this.consumer = consumer;
          if (params == null) {
            params = {};
          }
          this.identifier = JSON.stringify(params);
          extend(this, mixin);
        }

        Subscription.prototype.perform = function(action, data) {
          if (data == null) {
            data = {};
          }
          data.action = action;
          return this.send(data);
        };

        Subscription.prototype.send = function(data) {
          return this.consumer.send({
            command: "message",
            identifier: this.identifier,
            data: JSON.stringify(data)
          });
        };

        Subscription.prototype.unsubscribe = function() {
          return this.consumer.subscriptions.remove(this);
        };

        extend = function(object, properties) {
          var key, value;
          if (properties != null) {
            for (key in properties) {
              value = properties[key];
              object[key] = value;
            }
          }
          return object;
        };

        return Subscription;

      })();

    }).call(this);
    (function() {
      ActionCable.Consumer = (function() {
        function Consumer(url) {
          this.url = url;
          this.subscriptions = new ActionCable.Subscriptions(this);
          this.connection = new ActionCable.Connection(this);
        }

        Consumer.prototype.send = function(data) {
          return this.connection.send(data);
        };

        Consumer.prototype.connect = function() {
          return this.connection.open();
        };

        Consumer.prototype.disconnect = function() {
          return this.connection.close({
            allowReconnect: false
          });
        };

        Consumer.prototype.ensureActiveConnection = function() {
          if (!this.connection.isActive()) {
            return this.connection.open();
          }
        };

        return Consumer;

      })();

    }).call(this);
  }).call(this);

  if (typeof module === "object" && module.exports) {
    module.exports = ActionCable;
  } else if (typeof define === "function" && define.amd) {
    define(ActionCable);
  }
}).call(this);
// Action Cable provides the framework to deal with WebSockets in Rails.
// You can generate new channels where WebSocket features live using the rails generate channel command.
//




(function() {
  this.App || (this.App = {});

  App.cable = ActionCable.createConsumer();

}).call(this);
(function() {


}).call(this);
!function(){/*

 Copyright (C) 2006 Google Inc.

 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at

      http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
*/
window.PR_SHOULD_USE_CONTINUATION=!0;
(function(){function T(a){function d(e){var b=e.charCodeAt(0);if(92!==b)return b;var a=e.charAt(1);return(b=w[a])?b:"0"<=a&&"7">=a?parseInt(e.substring(1),8):"u"===a||"x"===a?parseInt(e.substring(2),16):e.charCodeAt(1)}function f(e){if(32>e)return(16>e?"\\x0":"\\x")+e.toString(16);e=String.fromCharCode(e);return"\\"===e||"-"===e||"]"===e||"^"===e?"\\"+e:e}function b(e){var b=e.substring(1,e.length-1).match(/\\u[0-9A-Fa-f]{4}|\\x[0-9A-Fa-f]{2}|\\[0-3][0-7]{0,2}|\\[0-7]{1,2}|\\[\s\S]|-|[^-\\]/g);e=
[];var a="^"===b[0],c=["["];a&&c.push("^");for(var a=a?1:0,g=b.length;a<g;++a){var h=b[a];if(/\\[bdsw]/i.test(h))c.push(h);else{var h=d(h),k;a+2<g&&"-"===b[a+1]?(k=d(b[a+2]),a+=2):k=h;e.push([h,k]);65>k||122<h||(65>k||90<h||e.push([Math.max(65,h)|32,Math.min(k,90)|32]),97>k||122<h||e.push([Math.max(97,h)&-33,Math.min(k,122)&-33]))}}e.sort(function(e,a){return e[0]-a[0]||a[1]-e[1]});b=[];g=[];for(a=0;a<e.length;++a)h=e[a],h[0]<=g[1]+1?g[1]=Math.max(g[1],h[1]):b.push(g=h);for(a=0;a<b.length;++a)h=b[a],
c.push(f(h[0])),h[1]>h[0]&&(h[1]+1>h[0]&&c.push("-"),c.push(f(h[1])));c.push("]");return c.join("")}function v(e){for(var a=e.source.match(/(?:\[(?:[^\x5C\x5D]|\\[\s\S])*\]|\\u[A-Fa-f0-9]{4}|\\x[A-Fa-f0-9]{2}|\\[0-9]+|\\[^ux0-9]|\(\?[:!=]|[\(\)\^]|[^\x5B\x5C\(\)\^]+)/g),c=a.length,d=[],g=0,h=0;g<c;++g){var k=a[g];"("===k?++h:"\\"===k.charAt(0)&&(k=+k.substring(1))&&(k<=h?d[k]=-1:a[g]=f(k))}for(g=1;g<d.length;++g)-1===d[g]&&(d[g]=++A);for(h=g=0;g<c;++g)k=a[g],"("===k?(++h,d[h]||(a[g]="(?:")):"\\"===
k.charAt(0)&&(k=+k.substring(1))&&k<=h&&(a[g]="\\"+d[k]);for(g=0;g<c;++g)"^"===a[g]&&"^"!==a[g+1]&&(a[g]="");if(e.ignoreCase&&n)for(g=0;g<c;++g)k=a[g],e=k.charAt(0),2<=k.length&&"["===e?a[g]=b(k):"\\"!==e&&(a[g]=k.replace(/[a-zA-Z]/g,function(a){a=a.charCodeAt(0);return"["+String.fromCharCode(a&-33,a|32)+"]"}));return a.join("")}for(var A=0,n=!1,l=!1,m=0,c=a.length;m<c;++m){var p=a[m];if(p.ignoreCase)l=!0;else if(/[a-z]/i.test(p.source.replace(/\\u[0-9a-f]{4}|\\x[0-9a-f]{2}|\\[^ux]/gi,""))){n=!0;
l=!1;break}}for(var w={b:8,t:9,n:10,v:11,f:12,r:13},r=[],m=0,c=a.length;m<c;++m){p=a[m];if(p.global||p.multiline)throw Error(""+p);r.push("(?:"+v(p)+")")}return new RegExp(r.join("|"),l?"gi":"g")}function U(a,d){function f(a){var c=a.nodeType;if(1==c){if(!b.test(a.className)){for(c=a.firstChild;c;c=c.nextSibling)f(c);c=a.nodeName.toLowerCase();if("br"===c||"li"===c)v[l]="\n",n[l<<1]=A++,n[l++<<1|1]=a}}else if(3==c||4==c)c=a.nodeValue,c.length&&(c=d?c.replace(/\r\n?/g,"\n"):c.replace(/[ \t\r\n]+/g,
" "),v[l]=c,n[l<<1]=A,A+=c.length,n[l++<<1|1]=a)}var b=/(?:^|\s)nocode(?:\s|$)/,v=[],A=0,n=[],l=0;f(a);return{a:v.join("").replace(/\n$/,""),c:n}}function J(a,d,f,b,v){f&&(a={h:a,l:1,j:null,m:null,a:f,c:null,i:d,g:null},b(a),v.push.apply(v,a.g))}function V(a){for(var d=void 0,f=a.firstChild;f;f=f.nextSibling)var b=f.nodeType,d=1===b?d?a:f:3===b?W.test(f.nodeValue)?a:d:d;return d===a?void 0:d}function G(a,d){function f(a){for(var l=a.i,m=a.h,c=[l,"pln"],p=0,w=a.a.match(v)||[],r={},e=0,t=w.length;e<
t;++e){var z=w[e],q=r[z],g=void 0,h;if("string"===typeof q)h=!1;else{var k=b[z.charAt(0)];if(k)g=z.match(k[1]),q=k[0];else{for(h=0;h<A;++h)if(k=d[h],g=z.match(k[1])){q=k[0];break}g||(q="pln")}!(h=5<=q.length&&"lang-"===q.substring(0,5))||g&&"string"===typeof g[1]||(h=!1,q="src");h||(r[z]=q)}k=p;p+=z.length;if(h){h=g[1];var B=z.indexOf(h),D=B+h.length;g[2]&&(D=z.length-g[2].length,B=D-h.length);q=q.substring(5);J(m,l+k,z.substring(0,B),f,c);J(m,l+k+B,h,K(q,h),c);J(m,l+k+D,z.substring(D),f,c)}else c.push(l+
k,q)}a.g=c}var b={},v;(function(){for(var f=a.concat(d),l=[],m={},c=0,p=f.length;c<p;++c){var w=f[c],r=w[3];if(r)for(var e=r.length;0<=--e;)b[r.charAt(e)]=w;w=w[1];r=""+w;m.hasOwnProperty(r)||(l.push(w),m[r]=null)}l.push(/[\0-\uffff]/);v=T(l)})();var A=d.length;return f}function y(a){var d=[],f=[];a.tripleQuotedStrings?d.push(["str",/^(?:\'\'\'(?:[^\'\\]|\\[\s\S]|\'{1,2}(?=[^\']))*(?:\'\'\'|$)|\"\"\"(?:[^\"\\]|\\[\s\S]|\"{1,2}(?=[^\"]))*(?:\"\"\"|$)|\'(?:[^\\\']|\\[\s\S])*(?:\'|$)|\"(?:[^\\\"]|\\[\s\S])*(?:\"|$))/,
null,"'\""]):a.multiLineStrings?d.push(["str",/^(?:\'(?:[^\\\']|\\[\s\S])*(?:\'|$)|\"(?:[^\\\"]|\\[\s\S])*(?:\"|$)|\`(?:[^\\\`]|\\[\s\S])*(?:\`|$))/,null,"'\"`"]):d.push(["str",/^(?:\'(?:[^\\\'\r\n]|\\.)*(?:\'|$)|\"(?:[^\\\"\r\n]|\\.)*(?:\"|$))/,null,"\"'"]);a.verbatimStrings&&f.push(["str",/^@\"(?:[^\"]|\"\")*(?:\"|$)/,null]);var b=a.hashComments;b&&(a.cStyleComments?(1<b?d.push(["com",/^#(?:##(?:[^#]|#(?!##))*(?:###|$)|.*)/,null,"#"]):d.push(["com",/^#(?:(?:define|e(?:l|nd)if|else|error|ifn?def|include|line|pragma|undef|warning)\b|[^\r\n]*)/,
null,"#"]),f.push(["str",/^<(?:(?:(?:\.\.\/)*|\/?)(?:[\w-]+(?:\/[\w-]+)+)?[\w-]+\.h(?:h|pp|\+\+)?|[a-z]\w*)>/,null])):d.push(["com",/^#[^\r\n]*/,null,"#"]));a.cStyleComments&&(f.push(["com",/^\/\/[^\r\n]*/,null]),f.push(["com",/^\/\*[\s\S]*?(?:\*\/|$)/,null]));if(b=a.regexLiterals){var v=(b=1<b?"":"\n\r")?".":"[\\S\\s]";f.push(["lang-regex",RegExp("^(?:^^\\.?|[+-]|[!=]=?=?|\\#|%=?|&&?=?|\\(|\\*=?|[+\\-]=|->|\\/=?|::?|<<?=?|>>?>?=?|,|;|\\?|@|\\[|~|{|\\^\\^?=?|\\|\\|?=?|break|case|continue|delete|do|else|finally|instanceof|return|throw|try|typeof)\\s*("+
("/(?=[^/*"+b+"])(?:[^/\\x5B\\x5C"+b+"]|\\x5C"+v+"|\\x5B(?:[^\\x5C\\x5D"+b+"]|\\x5C"+v+")*(?:\\x5D|$))+/")+")")])}(b=a.types)&&f.push(["typ",b]);b=(""+a.keywords).replace(/^ | $/g,"");b.length&&f.push(["kwd",new RegExp("^(?:"+b.replace(/[\s,]+/g,"|")+")\\b"),null]);d.push(["pln",/^\s+/,null," \r\n\t\u00a0"]);b="^.[^\\s\\w.$@'\"`/\\\\]*";a.regexLiterals&&(b+="(?!s*/)");f.push(["lit",/^@[a-z_$][a-z_$@0-9]*/i,null],["typ",/^(?:[@_]?[A-Z]+[a-z][A-Za-z_$@0-9]*|\w+_t\b)/,null],["pln",/^[a-z_$][a-z_$@0-9]*/i,
null],["lit",/^(?:0x[a-f0-9]+|(?:\d(?:_\d+)*\d*(?:\.\d*)?|\.\d\+)(?:e[+\-]?\d+)?)[a-z]*/i,null,"0123456789"],["pln",/^\\[\s\S]?/,null],["pun",new RegExp(b),null]);return G(d,f)}function L(a,d,f){function b(a){var c=a.nodeType;if(1==c&&!A.test(a.className))if("br"===a.nodeName)v(a),a.parentNode&&a.parentNode.removeChild(a);else for(a=a.firstChild;a;a=a.nextSibling)b(a);else if((3==c||4==c)&&f){var d=a.nodeValue,q=d.match(n);q&&(c=d.substring(0,q.index),a.nodeValue=c,(d=d.substring(q.index+q[0].length))&&
a.parentNode.insertBefore(l.createTextNode(d),a.nextSibling),v(a),c||a.parentNode.removeChild(a))}}function v(a){function b(a,c){var d=c?a.cloneNode(!1):a,k=a.parentNode;if(k){var k=b(k,1),e=a.nextSibling;k.appendChild(d);for(var f=e;f;f=e)e=f.nextSibling,k.appendChild(f)}return d}for(;!a.nextSibling;)if(a=a.parentNode,!a)return;a=b(a.nextSibling,0);for(var d;(d=a.parentNode)&&1===d.nodeType;)a=d;c.push(a)}for(var A=/(?:^|\s)nocode(?:\s|$)/,n=/\r\n?|\n/,l=a.ownerDocument,m=l.createElement("li");a.firstChild;)m.appendChild(a.firstChild);
for(var c=[m],p=0;p<c.length;++p)b(c[p]);d===(d|0)&&c[0].setAttribute("value",d);var w=l.createElement("ol");w.className="linenums";d=Math.max(0,d-1|0)||0;for(var p=0,r=c.length;p<r;++p)m=c[p],m.className="L"+(p+d)%10,m.firstChild||m.appendChild(l.createTextNode("\u00a0")),w.appendChild(m);a.appendChild(w)}function t(a,d){for(var f=d.length;0<=--f;){var b=d[f];I.hasOwnProperty(b)?E.console&&console.warn("cannot override language handler %s",b):I[b]=a}}function K(a,d){a&&I.hasOwnProperty(a)||(a=/^\s*</.test(d)?
"default-markup":"default-code");return I[a]}function M(a){var d=a.j;try{var f=U(a.h,a.l),b=f.a;a.a=b;a.c=f.c;a.i=0;K(d,b)(a);var v=/\bMSIE\s(\d+)/.exec(navigator.userAgent),v=v&&8>=+v[1],d=/\n/g,A=a.a,n=A.length,f=0,l=a.c,m=l.length,b=0,c=a.g,p=c.length,w=0;c[p]=n;var r,e;for(e=r=0;e<p;)c[e]!==c[e+2]?(c[r++]=c[e++],c[r++]=c[e++]):e+=2;p=r;for(e=r=0;e<p;){for(var t=c[e],z=c[e+1],q=e+2;q+2<=p&&c[q+1]===z;)q+=2;c[r++]=t;c[r++]=z;e=q}c.length=r;var g=a.h;a="";g&&(a=g.style.display,g.style.display="none");
try{for(;b<m;){var h=l[b+2]||n,k=c[w+2]||n,q=Math.min(h,k),B=l[b+1],D;if(1!==B.nodeType&&(D=A.substring(f,q))){v&&(D=D.replace(d,"\r"));B.nodeValue=D;var N=B.ownerDocument,u=N.createElement("span");u.className=c[w+1];var y=B.parentNode;y.replaceChild(u,B);u.appendChild(B);f<h&&(l[b+1]=B=N.createTextNode(A.substring(q,h)),y.insertBefore(B,u.nextSibling))}f=q;f>=h&&(b+=2);f>=k&&(w+=2)}}finally{g&&(g.style.display=a)}}catch(x){E.console&&console.log(x&&x.stack||x)}}var E=window,C=["break,continue,do,else,for,if,return,while"],
F=[[C,"auto,case,char,const,default,double,enum,extern,float,goto,inline,int,long,register,restrict,short,signed,sizeof,static,struct,switch,typedef,union,unsigned,void,volatile"],"catch,class,delete,false,import,new,operator,private,protected,public,this,throw,true,try,typeof"],H=[F,"alignas,alignof,align_union,asm,axiom,bool,concept,concept_map,const_cast,constexpr,decltype,delegate,dynamic_cast,explicit,export,friend,generic,late_check,mutable,namespace,noexcept,noreturn,nullptr,property,reinterpret_cast,static_assert,static_cast,template,typeid,typename,using,virtual,where"],
O=[F,"abstract,assert,boolean,byte,extends,finally,final,implements,import,instanceof,interface,null,native,package,strictfp,super,synchronized,throws,transient"],P=[F,"abstract,add,alias,as,ascending,async,await,base,bool,by,byte,checked,decimal,delegate,descending,dynamic,event,finally,fixed,foreach,from,get,global,group,implicit,in,interface,internal,into,is,join,let,lock,null,object,out,override,orderby,params,partial,readonly,ref,remove,sbyte,sealed,select,set,stackalloc,string,select,uint,ulong,unchecked,unsafe,ushort,value,var,virtual,where,yield"],
F=[F,"abstract,async,await,constructor,debugger,enum,eval,export,function,get,implements,instanceof,interface,let,null,set,undefined,var,with,yield,Infinity,NaN"],Q=[C,"and,as,assert,class,def,del,elif,except,exec,finally,from,global,import,in,is,lambda,nonlocal,not,or,pass,print,raise,try,with,yield,False,True,None"],R=[C,"alias,and,begin,case,class,def,defined,elsif,end,ensure,false,in,module,next,nil,not,or,redo,rescue,retry,self,super,then,true,undef,unless,until,when,yield,BEGIN,END"],C=[C,"case,done,elif,esac,eval,fi,function,in,local,set,then,until"],
S=/^(DIR|FILE|array|vector|(de|priority_)?queue|(forward_)?list|stack|(const_)?(reverse_)?iterator|(unordered_)?(multi)?(set|map)|bitset|u?(int|float)\d*)\b/,W=/\S/,X=y({keywords:[H,P,O,F,"caller,delete,die,do,dump,elsif,eval,exit,foreach,for,goto,if,import,last,local,my,next,no,our,print,package,redo,require,sub,undef,unless,until,use,wantarray,while,BEGIN,END",Q,R,C],hashComments:!0,cStyleComments:!0,multiLineStrings:!0,regexLiterals:!0}),I={};t(X,["default-code"]);t(G([],[["pln",/^[^<?]+/],["dec",
/^<!\w[^>]*(?:>|$)/],["com",/^<\!--[\s\S]*?(?:-\->|$)/],["lang-",/^<\?([\s\S]+?)(?:\?>|$)/],["lang-",/^<%([\s\S]+?)(?:%>|$)/],["pun",/^(?:<[%?]|[%?]>)/],["lang-",/^<xmp\b[^>]*>([\s\S]+?)<\/xmp\b[^>]*>/i],["lang-js",/^<script\b[^>]*>([\s\S]*?)(<\/script\b[^>]*>)/i],["lang-css",/^<style\b[^>]*>([\s\S]*?)(<\/style\b[^>]*>)/i],["lang-in.tag",/^(<\/?[a-z][^<>]*>)/i]]),"default-markup htm html mxml xhtml xml xsl".split(" "));t(G([["pln",/^[\s]+/,null," \t\r\n"],["atv",/^(?:\"[^\"]*\"?|\'[^\']*\'?)/,null,
"\"'"]],[["tag",/^^<\/?[a-z](?:[\w.:-]*\w)?|\/?>$/i],["atn",/^(?!style[\s=]|on)[a-z](?:[\w:-]*\w)?/i],["lang-uq.val",/^=\s*([^>\'\"\s]*(?:[^>\'\"\s\/]|\/(?=\s)))/],["pun",/^[=<>\/]+/],["lang-js",/^on\w+\s*=\s*\"([^\"]+)\"/i],["lang-js",/^on\w+\s*=\s*\'([^\']+)\'/i],["lang-js",/^on\w+\s*=\s*([^\"\'>\s]+)/i],["lang-css",/^style\s*=\s*\"([^\"]+)\"/i],["lang-css",/^style\s*=\s*\'([^\']+)\'/i],["lang-css",/^style\s*=\s*([^\"\'>\s]+)/i]]),["in.tag"]);t(G([],[["atv",/^[\s\S]+/]]),["uq.val"]);t(y({keywords:H,
hashComments:!0,cStyleComments:!0,types:S}),"c cc cpp cxx cyc m".split(" "));t(y({keywords:"null,true,false"}),["json"]);t(y({keywords:P,hashComments:!0,cStyleComments:!0,verbatimStrings:!0,types:S}),["cs"]);t(y({keywords:O,cStyleComments:!0}),["java"]);t(y({keywords:C,hashComments:!0,multiLineStrings:!0}),["bash","bsh","csh","sh"]);t(y({keywords:Q,hashComments:!0,multiLineStrings:!0,tripleQuotedStrings:!0}),["cv","py","python"]);t(y({keywords:"caller,delete,die,do,dump,elsif,eval,exit,foreach,for,goto,if,import,last,local,my,next,no,our,print,package,redo,require,sub,undef,unless,until,use,wantarray,while,BEGIN,END",
hashComments:!0,multiLineStrings:!0,regexLiterals:2}),["perl","pl","pm"]);t(y({keywords:R,hashComments:!0,multiLineStrings:!0,regexLiterals:!0}),["rb","ruby"]);t(y({keywords:F,cStyleComments:!0,regexLiterals:!0}),["javascript","js","ts","typescript"]);t(y({keywords:"all,and,by,catch,class,else,extends,false,finally,for,if,in,is,isnt,loop,new,no,not,null,of,off,on,or,return,super,then,throw,true,try,unless,until,when,while,yes",hashComments:3,cStyleComments:!0,multilineStrings:!0,tripleQuotedStrings:!0,
regexLiterals:!0}),["coffee"]);t(G([],[["str",/^[\s\S]+/]]),["regex"]);var Y=E.PR={createSimpleLexer:G,registerLangHandler:t,sourceDecorator:y,PR_ATTRIB_NAME:"atn",PR_ATTRIB_VALUE:"atv",PR_COMMENT:"com",PR_DECLARATION:"dec",PR_KEYWORD:"kwd",PR_LITERAL:"lit",PR_NOCODE:"nocode",PR_PLAIN:"pln",PR_PUNCTUATION:"pun",PR_SOURCE:"src",PR_STRING:"str",PR_TAG:"tag",PR_TYPE:"typ",prettyPrintOne:E.prettyPrintOne=function(a,d,f){f=f||!1;d=d||null;var b=document.createElement("div");b.innerHTML="<pre>"+a+"</pre>";
b=b.firstChild;f&&L(b,f,!0);M({j:d,m:f,h:b,l:1,a:null,i:null,c:null,g:null});return b.innerHTML},prettyPrint:E.prettyPrint=function(a,d){function f(){for(var b=E.PR_SHOULD_USE_CONTINUATION?c.now()+250:Infinity;p<t.length&&c.now()<b;p++){for(var d=t[p],l=g,m=d;m=m.previousSibling;){var n=m.nodeType,u=(7===n||8===n)&&m.nodeValue;if(u?!/^\??prettify\b/.test(u):3!==n||/\S/.test(m.nodeValue))break;if(u){l={};u.replace(/\b(\w+)=([\w:.%+-]+)/g,function(a,b,c){l[b]=c});break}}m=d.className;if((l!==g||r.test(m))&&
!e.test(m)){n=!1;for(u=d.parentNode;u;u=u.parentNode)if(q.test(u.tagName)&&u.className&&r.test(u.className)){n=!0;break}if(!n){d.className+=" prettyprinted";n=l.lang;if(!n){var n=m.match(w),C;!n&&(C=V(d))&&z.test(C.tagName)&&(n=C.className.match(w));n&&(n=n[1])}if(y.test(d.tagName))u=1;else var u=d.currentStyle,x=v.defaultView,u=(u=u?u.whiteSpace:x&&x.getComputedStyle?x.getComputedStyle(d,null).getPropertyValue("white-space"):0)&&"pre"===u.substring(0,3);x=l.linenums;(x="true"===x||+x)||(x=(x=m.match(/\blinenums\b(?::(\d+))?/))?
x[1]&&x[1].length?+x[1]:!0:!1);x&&L(d,x,u);M({j:n,h:d,m:x,l:u,a:null,i:null,c:null,g:null})}}}p<t.length?E.setTimeout(f,250):"function"===typeof a&&a()}for(var b=d||document.body,v=b.ownerDocument||document,b=[b.getElementsByTagName("pre"),b.getElementsByTagName("code"),b.getElementsByTagName("xmp")],t=[],n=0;n<b.length;++n)for(var l=0,m=b[n].length;l<m;++l)t.push(b[n][l]);var b=null,c=Date;c.now||(c={now:function(){return+new Date}});var p=0,w=/\blang(?:uage)?-([\w.]+)(?!\S)/,r=/\bprettyprint\b/,
e=/\bprettyprinted\b/,y=/pre|xmp/i,z=/^code$/i,q=/^(?:pre|code|xmp)$/i,g={};f()}},H=E.define;"function"===typeof H&&H.amd&&H("google-code-prettify",[],function(){return Y})})();}()
;
!function(){/*

 Copyright (C) 2013 Google Inc.

 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at

      http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.

 Copyright (C) 2006 Google Inc.

 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at

      http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
*/
(function(){function ba(g){function k(){try{M.doScroll("left")}catch(g){t.setTimeout(k,50);return}z("poll")}function z(k){if("readystatechange"!=k.type||"complete"==A.readyState)("load"==k.type?t:A)[B](p+k.type,z,!1),!q&&(q=!0)&&g.call(t,k.type||k)}var Y=A.addEventListener,q=!1,C=!0,x=Y?"addEventListener":"attachEvent",B=Y?"removeEventListener":"detachEvent",p=Y?"":"on";if("complete"==A.readyState)g.call(t,"lazy");else{if(A.createEventObject&&M.doScroll){try{C=!t.frameElement}catch(da){}C&&k()}A[x](p+
"DOMContentLoaded",z,!1);A[x](p+"readystatechange",z,!1);t[x](p+"load",z,!1)}}function U(){V&&ba(function(){var g=N.length;ca(g?function(){for(var k=0;k<g;++k)(function(g){t.setTimeout(function(){t.exports[N[g]].apply(t,arguments)},0)})(k)}:void 0)})}for(var t=window,A=document,M=A.documentElement,O=A.head||A.getElementsByTagName("head")[0]||M,B="",F=A.getElementsByTagName("script"),q=F.length;0<=--q;){var P=F[q],Z=P.src.match(/^[^?#]*\/run_prettify\.js(\?[^#]*)?(?:#.*)?$/);if(Z){B=Z[1]||"";P.parentNode.removeChild(P);
break}}var V=!0,H=[],Q=[],N=[];B.replace(/[?&]([^&=]+)=([^&]+)/g,function(g,k,z){z=decodeURIComponent(z);k=decodeURIComponent(k);"autorun"==k?V=!/^[0fn]/i.test(z):"lang"==k?H.push(z):"skin"==k?Q.push(z):"callback"==k&&N.push(z)});q=0;for(B=H.length;q<B;++q)(function(){var g=A.createElement("script");g.onload=g.onerror=g.onreadystatechange=function(){!g||g.readyState&&!/loaded|complete/.test(g.readyState)||(g.onerror=g.onload=g.onreadystatechange=null,--T,T||t.setTimeout(U,0),g.parentNode&&g.parentNode.removeChild(g),
g=null)};g.type="text/javascript";g.src="https://cdn.rawgit.com/google/code-prettify/master/loader/lang-"+encodeURIComponent(H[q])+".js";O.insertBefore(g,O.firstChild)})(H[q]);for(var T=H.length,F=[],q=0,B=Q.length;q<B;++q)F.push("https://cdn.rawgit.com/google/code-prettify/master/loader/skins/"+encodeURIComponent(Q[q])+".css");F.push("https://cdn.rawgit.com/google/code-prettify/master/loader/prettify.css");(function(g){function k(q){if(q!==z){var t=A.createElement("link");t.rel="stylesheet";t.type=
"text/css";q+1<z&&(t.error=t.onerror=function(){k(q+1)});t.href=g[q];O.appendChild(t)}}var z=g.length;k(0)})(F);var ca=function(){window.PR_SHOULD_USE_CONTINUATION=!0;var g;(function(){function k(a){function d(e){var b=e.charCodeAt(0);if(92!==b)return b;var a=e.charAt(1);return(b=W[a])?b:"0"<=a&&"7">=a?parseInt(e.substring(1),8):"u"===a||"x"===a?parseInt(e.substring(2),16):e.charCodeAt(1)}function f(e){if(32>e)return(16>e?"\\x0":"\\x")+e.toString(16);e=String.fromCharCode(e);return"\\"===e||"-"===
e||"]"===e||"^"===e?"\\"+e:e}function b(e){var b=e.substring(1,e.length-1).match(/\\u[0-9A-Fa-f]{4}|\\x[0-9A-Fa-f]{2}|\\[0-3][0-7]{0,2}|\\[0-7]{1,2}|\\[\s\S]|-|[^-\\]/g);e=[];var a="^"===b[0],c=["["];a&&c.push("^");for(var a=a?1:0,h=b.length;a<h;++a){var l=b[a];if(/\\[bdsw]/i.test(l))c.push(l);else{var l=d(l),n;a+2<h&&"-"===b[a+1]?(n=d(b[a+2]),a+=2):n=l;e.push([l,n]);65>n||122<l||(65>n||90<l||e.push([Math.max(65,l)|32,Math.min(n,90)|32]),97>n||122<l||e.push([Math.max(97,l)&-33,Math.min(n,122)&-33]))}}e.sort(function(e,
a){return e[0]-a[0]||a[1]-e[1]});b=[];h=[];for(a=0;a<e.length;++a)l=e[a],l[0]<=h[1]+1?h[1]=Math.max(h[1],l[1]):b.push(h=l);for(a=0;a<b.length;++a)l=b[a],c.push(f(l[0])),l[1]>l[0]&&(l[1]+1>l[0]&&c.push("-"),c.push(f(l[1])));c.push("]");return c.join("")}function g(e){for(var a=e.source.match(/(?:\[(?:[^\x5C\x5D]|\\[\s\S])*\]|\\u[A-Fa-f0-9]{4}|\\x[A-Fa-f0-9]{2}|\\[0-9]+|\\[^ux0-9]|\(\?[:!=]|[\(\)\^]|[^\x5B\x5C\(\)\^]+)/g),c=a.length,d=[],h=0,l=0;h<c;++h){var n=a[h];"("===n?++l:"\\"===n.charAt(0)&&(n=
+n.substring(1))&&(n<=l?d[n]=-1:a[h]=f(n))}for(h=1;h<d.length;++h)-1===d[h]&&(d[h]=++k);for(l=h=0;h<c;++h)n=a[h],"("===n?(++l,d[l]||(a[h]="(?:")):"\\"===n.charAt(0)&&(n=+n.substring(1))&&n<=l&&(a[h]="\\"+d[n]);for(h=0;h<c;++h)"^"===a[h]&&"^"!==a[h+1]&&(a[h]="");if(e.ignoreCase&&I)for(h=0;h<c;++h)n=a[h],e=n.charAt(0),2<=n.length&&"["===e?a[h]=b(n):"\\"!==e&&(a[h]=n.replace(/[a-zA-Z]/g,function(a){a=a.charCodeAt(0);return"["+String.fromCharCode(a&-33,a|32)+"]"}));return a.join("")}for(var k=0,I=!1,
m=!1,J=0,c=a.length;J<c;++J){var r=a[J];if(r.ignoreCase)m=!0;else if(/[a-z]/i.test(r.source.replace(/\\u[0-9a-f]{4}|\\x[0-9a-f]{2}|\\[^ux]/gi,""))){I=!0;m=!1;break}}for(var W={b:8,t:9,n:10,v:11,f:12,r:13},u=[],J=0,c=a.length;J<c;++J){r=a[J];if(r.global||r.multiline)throw Error(""+r);u.push("(?:"+g(r)+")")}return new RegExp(u.join("|"),m?"gi":"g")}function q(a,d){function f(a){var c=a.nodeType;if(1==c){if(!b.test(a.className)){for(c=a.firstChild;c;c=c.nextSibling)f(c);c=a.nodeName.toLowerCase();if("br"===
c||"li"===c)g[m]="\n",I[m<<1]=k++,I[m++<<1|1]=a}}else if(3==c||4==c)c=a.nodeValue,c.length&&(c=d?c.replace(/\r\n?/g,"\n"):c.replace(/[ \t\r\n]+/g," "),g[m]=c,I[m<<1]=k,k+=c.length,I[m++<<1|1]=a)}var b=/(?:^|\s)nocode(?:\s|$)/,g=[],k=0,I=[],m=0;f(a);return{a:g.join("").replace(/\n$/,""),c:I}}function t(a,d,f,b,g){f&&(a={h:a,l:1,j:null,m:null,a:f,c:null,i:d,g:null},b(a),g.push.apply(g,a.g))}function A(a){for(var d=void 0,f=a.firstChild;f;f=f.nextSibling)var b=f.nodeType,d=1===b?d?a:f:3===b?T.test(f.nodeValue)?
a:d:d;return d===a?void 0:d}function C(a,d){function f(a){for(var m=a.i,k=a.h,c=[m,"pln"],r=0,W=a.a.match(g)||[],u={},e=0,q=W.length;e<q;++e){var D=W[e],w=u[D],h=void 0,l;if("string"===typeof w)l=!1;else{var n=b[D.charAt(0)];if(n)h=D.match(n[1]),w=n[0];else{for(l=0;l<p;++l)if(n=d[l],h=D.match(n[1])){w=n[0];break}h||(w="pln")}!(l=5<=w.length&&"lang-"===w.substring(0,5))||h&&"string"===typeof h[1]||(l=!1,w="src");l||(u[D]=w)}n=r;r+=D.length;if(l){l=h[1];var E=D.indexOf(l),G=E+l.length;h[2]&&(G=D.length-
h[2].length,E=G-l.length);w=w.substring(5);t(k,m+n,D.substring(0,E),f,c);t(k,m+n+E,l,F(w,l),c);t(k,m+n+G,D.substring(G),f,c)}else c.push(m+n,w)}a.g=c}var b={},g;(function(){for(var f=a.concat(d),m=[],p={},c=0,r=f.length;c<r;++c){var q=f[c],u=q[3];if(u)for(var e=u.length;0<=--e;)b[u.charAt(e)]=q;q=q[1];u=""+q;p.hasOwnProperty(u)||(m.push(q),p[u]=null)}m.push(/[\0-\uffff]/);g=k(m)})();var p=d.length;return f}function x(a){var d=[],f=[];a.tripleQuotedStrings?d.push(["str",/^(?:\'\'\'(?:[^\'\\]|\\[\s\S]|\'{1,2}(?=[^\']))*(?:\'\'\'|$)|\"\"\"(?:[^\"\\]|\\[\s\S]|\"{1,2}(?=[^\"]))*(?:\"\"\"|$)|\'(?:[^\\\']|\\[\s\S])*(?:\'|$)|\"(?:[^\\\"]|\\[\s\S])*(?:\"|$))/,
null,"'\""]):a.multiLineStrings?d.push(["str",/^(?:\'(?:[^\\\']|\\[\s\S])*(?:\'|$)|\"(?:[^\\\"]|\\[\s\S])*(?:\"|$)|\`(?:[^\\\`]|\\[\s\S])*(?:\`|$))/,null,"'\"`"]):d.push(["str",/^(?:\'(?:[^\\\'\r\n]|\\.)*(?:\'|$)|\"(?:[^\\\"\r\n]|\\.)*(?:\"|$))/,null,"\"'"]);a.verbatimStrings&&f.push(["str",/^@\"(?:[^\"]|\"\")*(?:\"|$)/,null]);var b=a.hashComments;b&&(a.cStyleComments?(1<b?d.push(["com",/^#(?:##(?:[^#]|#(?!##))*(?:###|$)|.*)/,null,"#"]):d.push(["com",/^#(?:(?:define|e(?:l|nd)if|else|error|ifn?def|include|line|pragma|undef|warning)\b|[^\r\n]*)/,
null,"#"]),f.push(["str",/^<(?:(?:(?:\.\.\/)*|\/?)(?:[\w-]+(?:\/[\w-]+)+)?[\w-]+\.h(?:h|pp|\+\+)?|[a-z]\w*)>/,null])):d.push(["com",/^#[^\r\n]*/,null,"#"]));a.cStyleComments&&(f.push(["com",/^\/\/[^\r\n]*/,null]),f.push(["com",/^\/\*[\s\S]*?(?:\*\/|$)/,null]));if(b=a.regexLiterals){var g=(b=1<b?"":"\n\r")?".":"[\\S\\s]";f.push(["lang-regex",RegExp("^(?:^^\\.?|[+-]|[!=]=?=?|\\#|%=?|&&?=?|\\(|\\*=?|[+\\-]=|->|\\/=?|::?|<<?=?|>>?>?=?|,|;|\\?|@|\\[|~|{|\\^\\^?=?|\\|\\|?=?|break|case|continue|delete|do|else|finally|instanceof|return|throw|try|typeof)\\s*("+
("/(?=[^/*"+b+"])(?:[^/\\x5B\\x5C"+b+"]|\\x5C"+g+"|\\x5B(?:[^\\x5C\\x5D"+b+"]|\\x5C"+g+")*(?:\\x5D|$))+/")+")")])}(b=a.types)&&f.push(["typ",b]);b=(""+a.keywords).replace(/^ | $/g,"");b.length&&f.push(["kwd",new RegExp("^(?:"+b.replace(/[\s,]+/g,"|")+")\\b"),null]);d.push(["pln",/^\s+/,null," \r\n\t\u00a0"]);b="^.[^\\s\\w.$@'\"`/\\\\]*";a.regexLiterals&&(b+="(?!s*/)");f.push(["lit",/^@[a-z_$][a-z_$@0-9]*/i,null],["typ",/^(?:[@_]?[A-Z]+[a-z][A-Za-z_$@0-9]*|\w+_t\b)/,null],["pln",/^[a-z_$][a-z_$@0-9]*/i,
null],["lit",/^(?:0x[a-f0-9]+|(?:\d(?:_\d+)*\d*(?:\.\d*)?|\.\d\+)(?:e[+\-]?\d+)?)[a-z]*/i,null,"0123456789"],["pln",/^\\[\s\S]?/,null],["pun",new RegExp(b),null]);return C(d,f)}function B(a,d,f){function b(a){var c=a.nodeType;if(1==c&&!k.test(a.className))if("br"===a.nodeName)g(a),a.parentNode&&a.parentNode.removeChild(a);else for(a=a.firstChild;a;a=a.nextSibling)b(a);else if((3==c||4==c)&&f){var d=a.nodeValue,p=d.match(q);p&&(c=d.substring(0,p.index),a.nodeValue=c,(d=d.substring(p.index+p[0].length))&&
a.parentNode.insertBefore(m.createTextNode(d),a.nextSibling),g(a),c||a.parentNode.removeChild(a))}}function g(a){function b(a,c){var d=c?a.cloneNode(!1):a,n=a.parentNode;if(n){var n=b(n,1),e=a.nextSibling;n.appendChild(d);for(var f=e;f;f=e)e=f.nextSibling,n.appendChild(f)}return d}for(;!a.nextSibling;)if(a=a.parentNode,!a)return;a=b(a.nextSibling,0);for(var d;(d=a.parentNode)&&1===d.nodeType;)a=d;c.push(a)}for(var k=/(?:^|\s)nocode(?:\s|$)/,q=/\r\n?|\n/,m=a.ownerDocument,p=m.createElement("li");a.firstChild;)p.appendChild(a.firstChild);
for(var c=[p],r=0;r<c.length;++r)b(c[r]);d===(d|0)&&c[0].setAttribute("value",d);var t=m.createElement("ol");t.className="linenums";d=Math.max(0,d-1|0)||0;for(var r=0,u=c.length;r<u;++r)p=c[r],p.className="L"+(r+d)%10,p.firstChild||p.appendChild(m.createTextNode("\u00a0")),t.appendChild(p);a.appendChild(t)}function p(a,d){for(var f=d.length;0<=--f;){var b=d[f];X.hasOwnProperty(b)?R.console&&console.warn("cannot override language handler %s",b):X[b]=a}}function F(a,d){a&&X.hasOwnProperty(a)||(a=/^\s*</.test(d)?
"default-markup":"default-code");return X[a]}function H(a){var d=a.j;try{var f=q(a.h,a.l),b=f.a;a.a=b;a.c=f.c;a.i=0;F(d,b)(a);var g=/\bMSIE\s(\d+)/.exec(navigator.userAgent),g=g&&8>=+g[1],d=/\n/g,p=a.a,k=p.length,f=0,m=a.c,t=m.length,b=0,c=a.g,r=c.length,x=0;c[r]=k;var u,e;for(e=u=0;e<r;)c[e]!==c[e+2]?(c[u++]=c[e++],c[u++]=c[e++]):e+=2;r=u;for(e=u=0;e<r;){for(var A=c[e],D=c[e+1],w=e+2;w+2<=r&&c[w+1]===D;)w+=2;c[u++]=A;c[u++]=D;e=w}c.length=u;var h=a.h;a="";h&&(a=h.style.display,h.style.display="none");
try{for(;b<t;){var l=m[b+2]||k,n=c[x+2]||k,w=Math.min(l,n),E=m[b+1],G;if(1!==E.nodeType&&(G=p.substring(f,w))){g&&(G=G.replace(d,"\r"));E.nodeValue=G;var aa=E.ownerDocument,v=aa.createElement("span");v.className=c[x+1];var B=E.parentNode;B.replaceChild(v,E);v.appendChild(E);f<l&&(m[b+1]=E=aa.createTextNode(p.substring(w,l)),B.insertBefore(E,v.nextSibling))}f=w;f>=l&&(b+=2);f>=n&&(x+=2)}}finally{h&&(h.style.display=a)}}catch(y){R.console&&console.log(y&&y.stack||y)}}var R=window,K=["break,continue,do,else,for,if,return,while"],
L=[[K,"auto,case,char,const,default,double,enum,extern,float,goto,inline,int,long,register,restrict,short,signed,sizeof,static,struct,switch,typedef,union,unsigned,void,volatile"],"catch,class,delete,false,import,new,operator,private,protected,public,this,throw,true,try,typeof"],S=[L,"alignas,alignof,align_union,asm,axiom,bool,concept,concept_map,const_cast,constexpr,decltype,delegate,dynamic_cast,explicit,export,friend,generic,late_check,mutable,namespace,noexcept,noreturn,nullptr,property,reinterpret_cast,static_assert,static_cast,template,typeid,typename,using,virtual,where"],
M=[L,"abstract,assert,boolean,byte,extends,finally,final,implements,import,instanceof,interface,null,native,package,strictfp,super,synchronized,throws,transient"],N=[L,"abstract,add,alias,as,ascending,async,await,base,bool,by,byte,checked,decimal,delegate,descending,dynamic,event,finally,fixed,foreach,from,get,global,group,implicit,in,interface,internal,into,is,join,let,lock,null,object,out,override,orderby,params,partial,readonly,ref,remove,sbyte,sealed,select,set,stackalloc,string,select,uint,ulong,unchecked,unsafe,ushort,value,var,virtual,where,yield"],
L=[L,"abstract,async,await,constructor,debugger,enum,eval,export,function,get,implements,instanceof,interface,let,null,set,undefined,var,with,yield,Infinity,NaN"],O=[K,"and,as,assert,class,def,del,elif,except,exec,finally,from,global,import,in,is,lambda,nonlocal,not,or,pass,print,raise,try,with,yield,False,True,None"],P=[K,"alias,and,begin,case,class,def,defined,elsif,end,ensure,false,in,module,next,nil,not,or,redo,rescue,retry,self,super,then,true,undef,unless,until,when,yield,BEGIN,END"],K=[K,"case,done,elif,esac,eval,fi,function,in,local,set,then,until"],
Q=/^(DIR|FILE|array|vector|(de|priority_)?queue|(forward_)?list|stack|(const_)?(reverse_)?iterator|(unordered_)?(multi)?(set|map)|bitset|u?(int|float)\d*)\b/,T=/\S/,U=x({keywords:[S,N,M,L,"caller,delete,die,do,dump,elsif,eval,exit,foreach,for,goto,if,import,last,local,my,next,no,our,print,package,redo,require,sub,undef,unless,until,use,wantarray,while,BEGIN,END",O,P,K],hashComments:!0,cStyleComments:!0,multiLineStrings:!0,regexLiterals:!0}),X={};p(U,["default-code"]);p(C([],[["pln",/^[^<?]+/],["dec",
/^<!\w[^>]*(?:>|$)/],["com",/^<\!--[\s\S]*?(?:-\->|$)/],["lang-",/^<\?([\s\S]+?)(?:\?>|$)/],["lang-",/^<%([\s\S]+?)(?:%>|$)/],["pun",/^(?:<[%?]|[%?]>)/],["lang-",/^<xmp\b[^>]*>([\s\S]+?)<\/xmp\b[^>]*>/i],["lang-js",/^<script\b[^>]*>([\s\S]*?)(<\/script\b[^>]*>)/i],["lang-css",/^<style\b[^>]*>([\s\S]*?)(<\/style\b[^>]*>)/i],["lang-in.tag",/^(<\/?[a-z][^<>]*>)/i]]),"default-markup htm html mxml xhtml xml xsl".split(" "));p(C([["pln",/^[\s]+/,null," \t\r\n"],["atv",/^(?:\"[^\"]*\"?|\'[^\']*\'?)/,null,
"\"'"]],[["tag",/^^<\/?[a-z](?:[\w.:-]*\w)?|\/?>$/i],["atn",/^(?!style[\s=]|on)[a-z](?:[\w:-]*\w)?/i],["lang-uq.val",/^=\s*([^>\'\"\s]*(?:[^>\'\"\s\/]|\/(?=\s)))/],["pun",/^[=<>\/]+/],["lang-js",/^on\w+\s*=\s*\"([^\"]+)\"/i],["lang-js",/^on\w+\s*=\s*\'([^\']+)\'/i],["lang-js",/^on\w+\s*=\s*([^\"\'>\s]+)/i],["lang-css",/^style\s*=\s*\"([^\"]+)\"/i],["lang-css",/^style\s*=\s*\'([^\']+)\'/i],["lang-css",/^style\s*=\s*([^\"\'>\s]+)/i]]),["in.tag"]);p(C([],[["atv",/^[\s\S]+/]]),["uq.val"]);p(x({keywords:S,
hashComments:!0,cStyleComments:!0,types:Q}),"c cc cpp cxx cyc m".split(" "));p(x({keywords:"null,true,false"}),["json"]);p(x({keywords:N,hashComments:!0,cStyleComments:!0,verbatimStrings:!0,types:Q}),["cs"]);p(x({keywords:M,cStyleComments:!0}),["java"]);p(x({keywords:K,hashComments:!0,multiLineStrings:!0}),["bash","bsh","csh","sh"]);p(x({keywords:O,hashComments:!0,multiLineStrings:!0,tripleQuotedStrings:!0}),["cv","py","python"]);p(x({keywords:"caller,delete,die,do,dump,elsif,eval,exit,foreach,for,goto,if,import,last,local,my,next,no,our,print,package,redo,require,sub,undef,unless,until,use,wantarray,while,BEGIN,END",
hashComments:!0,multiLineStrings:!0,regexLiterals:2}),["perl","pl","pm"]);p(x({keywords:P,hashComments:!0,multiLineStrings:!0,regexLiterals:!0}),["rb","ruby"]);p(x({keywords:L,cStyleComments:!0,regexLiterals:!0}),["javascript","js","ts","typescript"]);p(x({keywords:"all,and,by,catch,class,else,extends,false,finally,for,if,in,is,isnt,loop,new,no,not,null,of,off,on,or,return,super,then,throw,true,try,unless,until,when,while,yes",hashComments:3,cStyleComments:!0,multilineStrings:!0,tripleQuotedStrings:!0,
regexLiterals:!0}),["coffee"]);p(C([],[["str",/^[\s\S]+/]]),["regex"]);var V=R.PR={createSimpleLexer:C,registerLangHandler:p,sourceDecorator:x,PR_ATTRIB_NAME:"atn",PR_ATTRIB_VALUE:"atv",PR_COMMENT:"com",PR_DECLARATION:"dec",PR_KEYWORD:"kwd",PR_LITERAL:"lit",PR_NOCODE:"nocode",PR_PLAIN:"pln",PR_PUNCTUATION:"pun",PR_SOURCE:"src",PR_STRING:"str",PR_TAG:"tag",PR_TYPE:"typ",prettyPrintOne:function(a,d,f){f=f||!1;d=d||null;var b=document.createElement("div");b.innerHTML="<pre>"+a+"</pre>";b=b.firstChild;
f&&B(b,f,!0);H({j:d,m:f,h:b,l:1,a:null,i:null,c:null,g:null});return b.innerHTML},prettyPrint:g=g=function(a,d){function f(){for(var b=R.PR_SHOULD_USE_CONTINUATION?c.now()+250:Infinity;r<p.length&&c.now()<b;r++){for(var d=p[r],k=h,q=d;q=q.previousSibling;){var m=q.nodeType,v=(7===m||8===m)&&q.nodeValue;if(v?!/^\??prettify\b/.test(v):3!==m||/\S/.test(q.nodeValue))break;if(v){k={};v.replace(/\b(\w+)=([\w:.%+-]+)/g,function(a,b,c){k[b]=c});break}}q=d.className;if((k!==h||u.test(q))&&!e.test(q)){m=!1;
for(v=d.parentNode;v;v=v.parentNode)if(w.test(v.tagName)&&v.className&&u.test(v.className)){m=!0;break}if(!m){d.className+=" prettyprinted";m=k.lang;if(!m){var m=q.match(t),C;!m&&(C=A(d))&&z.test(C.tagName)&&(m=C.className.match(t));m&&(m=m[1])}if(x.test(d.tagName))v=1;else var v=d.currentStyle,y=g.defaultView,v=(v=v?v.whiteSpace:y&&y.getComputedStyle?y.getComputedStyle(d,null).getPropertyValue("white-space"):0)&&"pre"===v.substring(0,3);y=k.linenums;(y="true"===y||+y)||(y=(y=q.match(/\blinenums\b(?::(\d+))?/))?
y[1]&&y[1].length?+y[1]:!0:!1);y&&B(d,y,v);H({j:m,h:d,m:y,l:v,a:null,i:null,c:null,g:null})}}}r<p.length?R.setTimeout(f,250):"function"===typeof a&&a()}for(var b=d||document.body,g=b.ownerDocument||document,b=[b.getElementsByTagName("pre"),b.getElementsByTagName("code"),b.getElementsByTagName("xmp")],p=[],k=0;k<b.length;++k)for(var m=0,q=b[k].length;m<q;++m)p.push(b[k][m]);var b=null,c=Date;c.now||(c={now:function(){return+new Date}});var r=0,t=/\blang(?:uage)?-([\w.]+)(?!\S)/,u=/\bprettyprint\b/,
e=/\bprettyprinted\b/,x=/pre|xmp/i,z=/^code$/i,w=/^(?:pre|code|xmp)$/i,h={};f()}},S=R.define;"function"===typeof S&&S.amd&&S("google-code-prettify",[],function(){return V})})();return g}();T||t.setTimeout(U,0)})();}()
;
//
// tc.platform.browser.Event
//

window.Event = function(evt)
{
    if(evt){
        this.srcEvent = evt;
        this.keyCode = evt.keyCode;
        this.charCode = evt.charCode;
        this.target = evt.target;
    } else{
        this.srcEvent = window.event;
        this.keyCode = window.event.keyCode;
        this.charCode = window.event.keyCode;
        this.target = window.event.srcElement;
    }
    this.clientX = this.srcEvent.clientX;
    this.clientY = this.srcEvent.clientY;

    return this;
};

window.Event.addEventListener = function(node, eventname, obj, fn)
{
    if(node.addEventListener) {
        var wrapperfn = function(e) {
            var e = new window.Event(e);
            return fn.apply(obj, [ e, node ]);
        };
        fn.wrapper = wrapperfn;
        node.addEventListener(eventname, wrapperfn, false);
    } else if(node.attachEvent) {
        var wrapperfn = function() {
            var e = new window.Event();
            return fn.apply(obj, [ e, node ]);
        };
        fn.wrapper = wrapperfn;
        node.attachEvent("on" + eventname, wrapperfn);
    } else {
        // write emulation
    }
};

window.Event.removeEventListener = function(node, eventname, obj, fn)
{
    if(node.removeEventListener) {
        node.removeEventListener(eventname, fn.wrapper, false);
    } else if(node.detachEvent) {
        node.detachEvent("on" + eventname, fn.wrapper);
    } else {
        // write emulation
    }
};
//
// window.Console
//

// getAbsolutePosition is not used

function getAbsolutePosition(element) {
    var r = { x: element.offsetLeft, y: element.offsetTop };
    if (element.offsetParent) {
	var tmp = getAbsolutePosition(element.offsetParent);
	r.x += tmp.x;
	r.y += tmp.y;
    }
    return r;
};

window.JavascriptConsole = function (what,name,stmt,evt,factor) {

    this.lineHeight = ((navigator.appName.indexOf("Microsoft")!=-1) ? 20 : 15);

    if (window.opera) {
        this.charWidth = 7.2;
    } else {
        this.charWidth = 8;
    }

    this.codePadding = 10;
    this.textPadding = 20;

    this.svgWidth = (stmt == "svg()") ? 400 : 0;

    this.sicpPath = "";

    window.javascript_statement = stmt;

    if (parseInt(navigator.appVersion)>3) {
        if (navigator.appName.indexOf("Microsoft")!=-1) {
            this._windowWidth = document.body.offsetWidth;
        } else { // (navigator.appName=="Netscape")
            this._windowWidth = window.innerWidth;
        }
    }

    // see book.css: subtract margins on left in px and right 4%
    this._textWidth =
        ((navigator.appName.indexOf("Microsoft")!=-1) ?
	    (this._windowWidth * 0.5) - 210  + 2 * this.textPadding
        : (this._windowWidth * 0.5) - 160 + 2 * this.textPadding);

    var pos = window.JavascriptConsole.find_pos(evt);

    xPos = pos[0];

    yPos = pos[1]+40;

    var lines = Math.min(this._count_lines(what),50);

    this._mainDiv = null;
    this._dragMode = 0;

    this._event = evt;

    this._name = name;

    this._displayString = "";

    var content =
    	'<table class="table table-condensed">' +
    	'<colgroup><col width="50%"/><col width="50%"/></colgroup>' +
    	'<tr>' +
            '<td align="left">' +
            '<button id="'+
    	this._name+'_eval_button">Evaluate</button>' +
    	'</td>' +
            '<td align="right">' +
            '<button onclick="window.JavascriptConsole.close(\''+
            this._name+'\');">Close</button>' +
    	'</td>' +
            '</tr>' +
            '</table>' +
    	'<table class="table table-condensed">' +
    	'<tr>' +
    	(( stmt == "svg()" ) ?
             '<td><embed id="embed_' + this._name + '"' +
    	 ' src="svg/svg.svg" type="image/svg+xml" width="400" height="400"></td>'
    	 : ''
    	)+
    	'<td><textarea class="popupoutput form-control" readonly="true" id="'+
    	this._name+'_result_textarea" cols="'+
            ((this._textWidth - this.svgWidth)* factor / this.charWidth) +
    	'" rows="' +
    	((stmt == "svg()") ? (this.svgWidth)/this.lineHeight : 8) +
    	'">' +
    	'</textarea></td>' +
    	'</tr>' +
            '</table>'
    	;

    this._codeHook = document.getElementById(name+"_div");

    this._mainDiv = document.createElement('div');
    // className especially for IE
    this._mainDiv.setAttribute('className',"popup");
    this._mainDiv.setAttribute('class',"popup");
    this._mainDiv.setAttribute('id',name);
    this._mainDiv.style.position = "absolute";
    //this._mainDiv.style.width = this._textWidth * factor + 2 * this.textPadding;
    this._mainDiv.style.width = this._codeHook.style.width
    this._mainDiv.style.left = xPos + "px";
    this._mainDiv.style.top = yPos + "px";
    this._mainDiv.style.zIndex = 4;

    this._mainDiv.innerHTML =
	   "<div class='popupinner'>" +
	    content +
        "</div>";


    this._codeHook.style.display = "block";
    this._codeHook.style.border = "solid 1px #424242"

    this._codeHook.style.left = (xPos + 20) + "px";
    this._codeHook.style.top = (yPos - 10) + "px";
    this._codeHook.style.zIndex = 5;

    this._codeHook.innerHTML = "";

    this._sourceObject = CodeMirror(this._codeHook, {
    	height: (lines * this.lineHeight + this.codePadding)+'px',
        //width: (this._textWidth * factor)+'px',
        mode: 'javascript',
        lineSeparator: '\n',
        tabMode: "indent",
    	value: what,
    	parserfile: ["tokenizejavascript.js", "parsejavascript.js"],
    	theme: "default",
        // path: "public/codemirror/",
        autoMatchParens: true
    });

    document.body.appendChild(this._mainDiv);

    // Hook mousedown for dragging
    window.Event.addEventListener(this._mainDiv, "mousedown", this,
        window.JavascriptConsole.prototype._drag_mousedown);

    this._resultTextarea = document.getElementById(name+"_result_textarea");

    var evalButton = document.getElementById(name+"_eval_button");
    var self = this;

    evalButton.onclick = function () {
   	    self.eval_javascript(self._name);
    };

    window.latestConsole = this;

    //if (stmt == "svg()") {
    //    this.svg_init();
    //}
}

window.JavascriptConsole.prototype.svg_init = function(s) {

}

window.JavascriptConsole.prototype._count_lines = function(s) {
    var counter = 1;
    for (i=0;i<s.length;i++)
	if (s.charAt(i) == '\n') counter++;
    return counter;
}

window.JavascriptConsole.prototype._get_height_factor = function() {
    return (window.XMLHttpRequest) ?
	(
	    (window.ActiveXObject) ?
		// IE 7
		17
		:
		// Opera, Safari, Firefox
		14
	)
    :
    //IE 6 and below
    15
    ;
}

window.JavascriptConsole.prototype._get_height_offset = function() {
    return (window.XMLHttpRequest) ?
	(
	    (window.ActiveXObject) ?
		// IE 7
		300
		:
		// Opera, Safari, Firefox
		250
	)
    :
    //IE 6 and below
    285
    ;
}

/********************
 *  Event Handlers  *
 ********************/

window.JavascriptConsole.prototype._close_click = function() {
    document.body.removeChild(this._mainDiv);
}

window.JavascriptConsole.prototype._drag_mousedown = function(evt) {
    this._mainDiv.style.zIndex ++;
    this._codeHook.style.zIndex ++;

    if (window.HTMLTextAreaElement && evt.target instanceof HTMLTextAreaElement) {
	this._dragMode = 0;
	return;
    }

    this._dragMode = 1;

    // Save initial window location
    this._drag_offsetLeft = this._mainDiv.offsetLeft;
    this._drag_offsetTop = this._mainDiv.offsetTop;

    // Save initial codeHook location
    this._drag_offsetLeftCodeHook = this._codeHook.offsetLeft;
    this._drag_offsetTopCodeHook = this._codeHook.offsetTop;

    // Save initial mouse down position
    this._drag_clientX = evt.clientX;
    this._drag_clientY = evt.clientY;

    // Save initial window scroll position
    if(typeof window.scrollY === "number") {
        this._drag_scrollX = window.scrollX;
        this._drag_scrollY = window.scrollY;
    } else if(typeof document.body.scrollTop === "number") {
        this._drag_scrollX = document.body.scrollLeft;
        this._drag_scrollY = document.body.scrollTop;
    }

    // Listen for mousemove and mouseup
    window.Event.addEventListener(document, "mousemove", this,
				  window.JavascriptConsole.prototype._drag_mousemove);
    window.Event.addEventListener(document, "mouseup", this,
				  window.JavascriptConsole.prototype._drag_mouseup);
}

window.JavascriptConsole.prototype._drag_mousemove = function(evt) {
    // Calculate movement delta (from initial mousedown position)
    var dx = evt.clientX - this._drag_clientX;
    var dy = evt.clientY - this._drag_clientY;

    // Adjust for the window scroll
    if(typeof window.scrollX === "number") {
        dx += (window.scrollX - this._drag_scrollX);
        dy += (window.scrollY - this._drag_scrollY);
    } else if(typeof document.body.scrollTop === "number") {
        dx += (document.body.scrollLeft - this._drag_scrollX);
        dy += (document.body.scrollTop - this._drag_scrollY);
    }

    // Do the move (from initial window position)
    switch (this._dragMode) {
    case 1:
        this._mainDiv.style.left = (this._drag_offsetLeft + dx) + "px";
        this._mainDiv.style.top = (this._drag_offsetTop + dy) + "px";
        this._codeHook.style.left = (this._drag_offsetLeftCodeHook + dx) + "px";
        this._codeHook.style.top = (this._drag_offsetTopCodeHook + dy) + "px";
        break;
    case 2:
        var w = this._drag_offsetWidth + dx, h = this._drag_offsetHeight + dy;
        if (w < 100) dx = (w = 100) - this._drag_offsetWidth;
        if (h < 50) dy = (h = 50) - this._drag_offsetHeight;
        this._mainDiv.style.width = w + "px";
        this._mainDiv.style.height = "auto";
        break;
    }

    return false;
}

window.JavascriptConsole.prototype._drag_mouseup = function(evt) {

    window.Event.removeEventListener(document, "mousemove", this,
				     this._drag_mousemove);
    window.Event.removeEventListener(document, "mouseup", this,
				     this._drag_mouseup);
    this._dragMode = 0;

    //	evt.target.style.cursor = "move";

    return false;
}

// from http://www.quirksmode.org/js/findpos.html

window.JavascriptConsole.find_pos = function(e) {
    var curtop = 0;
    var curleft = 0;
    var obj = e.target ? e.target : e.srcElement;

    if (obj && obj.offsetParent) {

    	do {
	    curleft += obj.offsetLeft;
	    curtop += obj.offsetTop;

	} while (obj = obj.offsetParent);
    }

    return [curleft,curtop];

}

window.JavascriptConsole.prototype.eval_javascript = function(nam) {
    window.name = nam;
    var svgdoc = null;

/*
    try {
	var embed = document.getElementById('embed_'+nam);
	svgdoc = embed.getSVGDocument();
    var svgobj = svgdoc.getElementById('outer-svg');
    var svgNS = "http://www.w3.org/2000/svg";
    var xlinkNS = "http://www.w3.org/1999/xlink";
    var newRect = document.createElementNS(svgNS,"rect");
    newRect.setAttributeNS(null,"width", 400);
    newRect.setAttributeNS(null,"height", 400);
    newRect.setAttributeNS(null,"x", 0);
    newRect.setAttributeNS(null,"y", 0);
    newRect.setAttributeNS(null,"fill","#dddddd");
    svgobj.appendChild(newRect);
    }
    catch(exception) {
	// ignore errors
    }
*/

    try {
        with (window) {
	           window.make_painter_from_url = function(url) {
                   return function(frame) {
                       var x0=frame[0][0];
		               var y0=frame[0][1];
                       var x1=frame[1][0][0];
                       var y1=frame[1][0][1];
                       var x2=frame[1][1][0][0];
                       var y2=frame[1][1][0][1];

		               var svgdoc = null;

                       var embed = document.getElementById('embed_'+name);

		               try {
                           svgdoc = embed.getSVGDocument();
		               } catch(exception) {
                           alert('error: embed: '+embed);
                           alert('error: svgdoc: '+svgdoc);
                       }

                       var svgobj = svgdoc.getElementById('outer-svg');
                       //svgobj.setAttribute("viewBox", "0 0 400 400");
                       //svgobj.setAttribute("width",400);
                       //svgobj.setAttribute("height",400);
                       var svgNS = "http://www.w3.org/2000/svg";
                       var xlinkNS = "http://www.w3.org/1999/xlink";

                       var newTransform = document.createElementNS(svgNS,"g");
                       var matrix_string = "matrix("+x1+","+(-1)*y1+","+
                            (-1)*x2+","+y2+","+400*(x0+x2)+","+400*(1-y0-y2)+")";

                       newTransform.setAttributeNS(null,"transform",matrix_string);
                       svgobj.appendChild(newTransform);

                       var newPict = document.createElementNS(svgNS,"image");
                       newPict.setAttributeNS(null,"x",0);
                       newPict.setAttributeNS(null,"y",0);
                       newPict.setAttributeNS(null,"width",400);
                       newPict.setAttributeNS(null,"height",400);
                       newPict.setAttributeNS(xlinkNS,"href",url);
                       //newPict.setAttributeNS(null, "viewBox", "0 0 400 400");
                       newTransform.appendChild(newPict);
                   };
               // make_painter_from_url()
               };
               // Wave & Rogers are not snippets but required as snippets
               window.wave = make_painter_from_url(
                   "http://www.comp.nus.edu.sg/~henz/sicp/img_original/my_wave.png");
               window.rogers = make_painter_from_url(
                "http://www.comp.nus.edu.sg/~henz/sicp/img_original/ch2-Z-G-30.gif");
               window.result = window.eval(this._sourceObject.getValue());
           }
           toShow = this.format(window.result);
       } catch ( ee ) {
	       toShow = 'Exception: '+ ee;
       }
    this.display(toShow);
}

window.JavascriptConsole.prototype.display = function(toShow) {
    this._displayString = this._displayString + '\n' + toShow + '\n';
    this._resultTextarea.value = this._displayString;
    this._resultTextarea.scrollTop = this._resultTextarea.scrollHeight;
}

window.JavascriptConsole.close = function(name) {
    document.body.removeChild(document.getElementById(name));
    var codeHook = document.getElementById(name+"_div");
    codeHook.style.display = "none";
}

// format: JavaScript value to string
// limit the recursion so that circularity does
// not lead to runtime errors
window.JavascriptConsole.prototype.format = function(x) {
    return this._format_it(x,10);
}

window.JavascriptConsole.prototype._format_it = function(x,d) {
    if (d == 0) return "...";
    if ( x == undefined || x == null || typeof x == "number"
	 || typeof x == "boolean" ) return x;
    else if (typeof x == "string") { var s = '"' + x + '"'; return s; }
    else if (typeof x == "object")
	if (x.tag == "exit") { return "";}
    else if (x instanceof Array) return this._format_array(x,d-1);
    else return this._format_object(x,d-1);
    else if (typeof x == "function")
	return x.toString();
}

window.JavascriptConsole.prototype._format_array = function(x,d) {
    var l = x.length;
    var s = "";
    for (var i = 0; i < l-1; i++)
	s += this._format_it(x[i],d) + ",";
    if (l > 0) s += this._format_it(x[l-1],d);
    return "[" + s + "]";
}

window.JavascriptConsole.prototype._format_object = function(x,d) {
    var s = "";
    for (var prop in x)
	s += prop + ":" + this._format_it(x[prop],d) + ",";
    return "{" + s.substring(0,s.length-1) + "}";
}
;
// communication of data between the main pages and
// the popup windows turned out to be tricky, because
// Opera does not allow attaching fields to the created
// window.

// roughly:
// all browsers except IE get their data from the name
// (key-data pairs separated by escape characters).
// IE is picky about characters in the name, so the
// data is attached to the window object.

function getHeightFactor() {
    return (window.XMLHttpRequest) ?
	(
	 (window.ActiveXObject) ?
	 // IE 7
	 17
	 :
	 // Opera, Safari, Firefox
	 14
	 )
	:
	//IE 6 and below
	15
	;
}

function getHeightOffset() {
    return (window.XMLHttpRequest) ?
	(
	 (window.ActiveXObject) ?
	 // IE 7
	 300
	 :
	 // Opera, Safari, Firefox
	 250
	 )
	:
	//IE 6 and below
	285
	;
}

function onMouseOver(obj) {
    obj.style.cursor='pointer';
}

function onMouseOverImg(obj) {
    obj.style.cursor='pointer';
    obj.style.border='solid thin';
    obj.style.borderColor='red';
}

function countLines(s) {
    var counter = 0;
    for (i=0;i<s.length;i++)
	if (s.charAt(i) == '\n') counter++;
    return counter;
}

// format: JavaScript value to string
// limit the recursion so that circularity does
// not lead to runtime errors
function format(x) {
    return formatIt(x,10);
}

function formatIt(x,d) {
    if (d == 0) return "...";
    if ( x == undefined || x == null || typeof x == "number" || typeof x == "boolean" ) return x;
    else if (typeof x == "string") { var s = '"' + x + '"'; return s; }
    else if (typeof x == "object")
        if (x.tag == "exit") { return "";}
	else if (x instanceof Array) return formatArray(x,d-1);
        else return formatObject(x,d-1);
    else if (typeof x == "function")
	return x.toString();
}

function formatArray(x,d) {
    var l = x.length;
    var s = "";
    for (var i = 0; i < l-1; i++)
	s += formatIt(x[i],d) + ",";
    if (l > 0) s += formatIt(x[l-1],d);
    return "[" + s + "]";
}

function formatObject(x,d) {
    var s = "";
    for (var prop in x)
	s += prop + ":" + formatIt(x[prop],d) + ",";
    return "{" + s.substring(0,s.length-1) + "}";
}

function evalScheme(where,what,accumulating) {
    theText = where;
    if (!window[where]) window[where] = '';
    if (!accumulating) {
	if (document['form_'+where].resultScheme.style.display == "none")
	    document['form_'+where].resultScheme.style.display = "";
	else document['form_'+where].resultScheme.style.display = "none";
	if (document['form_'+where].buttonScheme.style.display == "none")
	    document['form_'+where].buttonScheme.style.display = "";
	else document['form_'+where].buttonScheme.style.display = "none";
    }

    try {
	var output = schemeEval(what);
	window[where]
	    = (accumulating)
	    ? window[where] + '\n' + output + '\n'
	    : output;
	document['form_'+where].resultScheme.value
	    = window[where];
	document['form_'+where].resultScheme.scrollTop
	    = document['form_'+where].resultScheme.scrollHeight;
    } catch ( ee ) {
	var toShow = 'Error: ' + ee.Content();
	window[where]
	    = (accumulating)
	    ? window[where] + toShow + '\n'
	    : toShow;
	document['form_'+where].resultScheme.value
	    = window[where];
	document['form_'+where].resultScheme.scrollTop
	    = document['form_'+where].resultScheme.scrollHeight;
    }
};

var evalLib = {
    localEval: function (what) {
	window.what = what;
	with (window) {
	    window.result = window.eval(what); };
	return window.result;
    }
}

function evalJavaScript(where,what,accumulating) {
	theText = where;
	if (!window[where]) window[where] = '';
	if (!accumulating) {
	    if (document['form_'+where].resultJavaScript.style.display == "none")
		document['form_'+where].resultJavaScript.style.display = "";
	    else document['form_'+where].resultJavaScript.style.display = "none";
	    if (document['form_'+where].buttonJavaScript.style.display == "none")
		document['form_'+where].buttonJavaScript.style.display = "";
	    else document['form_'+where].buttonJavaScript.style.display = "none";
	}
	try {       var result;

	    var toShow = // (result==undefined && !accumulating)
		// ? 'Evaluation completed'
		//:
		format(evalLib.localEval(what));
	    window[where]
		= (accumulating)
		? window[where] + '\n' + toShow + '\n'
		: toShow;
	    document['form_'+where].resultJavaScript.value
		= window[where];
	    document['form_'+where].resultJavaScript.scrollTop
		= document['form_'+where].resultJavaScript.scrollHeight;
	} catch ( ee ) {
	    var toShow = 'Exception: '+ ee;
	    window[where]
		= (accumulating)
		? window[where] + toShow + '\n'
		: toShow;
	    document['form_'+where].resultJavaScript.value
		= window[where];
	    document['form_'+where].resultJavaScript.scrollTop
		= document['form_'+where].resultJavaScript.scrollHeight;
	}
}


function generateSchemeContent() {
    // once we get to execute this on IE, document.all
    // is there. Do the following for IE, and do the
    // else part for all other browsers.
    if (document.all) {
	var what = window.what;
	var where = window.where;
	var lines = window.lines;
	window.document.body.innerHTML =
	    'Scheme expression from Section '+
	    window.section +
	    '; click "Eval" to evaluate it.' +
	    '<form name="form_'+where+'">' +
	    '<table>' +
	    '<tr>' +
	    '<td>' +
	    '<textarea name="source" rows="' +
	    lines +
	    '" cols="80">' +
	    what +
	    '</textarea>' +
	    '</td>' +
	    '</tr>' +
	    '<tr>' +
	    '<td>' +
	    '<input name="buttonScheme" type="button" value="Eval" onclick="evalScheme(\''+
	    where +
	    '\',document.form_'+where+'.source.value,true)">' +
	    '</input>' +
	    '</td>' +
	    '</tr>' +
	    '<tr>' +
	    '<td>' +
	    '<textarea name="resultScheme" readonly="true" rows="8" cols="80">' +
	    '</textarea>' +
	    '</td>' +
	    '</tr>' +
	    '</table>' +
	    '</form>'
	    ;
	schemeInit();
    } else {
	// retrieve URL arguments, which serve
	// to pass content data to the window.
	// (see comment on Opera under popupScheme)
	var args = getArgs(window);
	var section = args.section;
	var where = args.where;
	var what = args.what;
	var lines = parseInt(args.lines);

	window.scheme_statement = args.scheme_statement;

	window.document.body.innerHTML =
	    'Scheme expression from Section '+
	    section +
	    '; click "Eval" to evaluate it.' +
	    '<form name="form_'+where+'">' +
	    '<table>' +
	    '<tr>' +
	    '<td>' +
	    '<textarea name="source" spellcheck="false" rows="' +
	    lines +
	    '" cols="80">' +
	    what +
	    '</textarea>' +
	    '</td>' +
	    '</tr>' +
	    '<tr>' +
	    '<td>' +
	    '<input name="buttonScheme" type="button" value="Eval" onclick="evalScheme(\''+
	    where +
	    '\',document.form_'+where+'.source.value,true)">' +
	    '</input>' +
	    '</td>' +
	    '</tr>' +
	    '<tr>' +
	    '<td>' +
	    '<textarea name="resultScheme" readonly="true" rows="8" cols="80">' +
	    '</textarea>' +
	    '</td>' +
	    '</tr>' +
	    '</table>' +
	    '</form>'
	    ;
	schemeInit();
    }
}

// The following characters are used as escape characters
// in order to separate arguments. Hopefully, they do not
// appear in any Scheme or JavaScript programs in the book.

var escape1 = "@";
var escape2 = "^";

// Note the trick to open an empty page first,
// and then have that page call generateSchemeContent().
// If the content is placed into innerHtml immediately,
// Firefox 2.0 will not display it.

// we pass relevant data as URL arguments;
// Opera does not preserve window attributes as in "win.lines = lines"

function popupScheme(where,what,section,stmt) {

    if (document.all) {
	var lines = countLines(what);
	var win = window.open("html_scheme/emptyScheme.html", "Evaluator_"+where,
			      "width=710,height="+((lines*getHeightFactor())+getHeightOffset())+",scrollbars=yes");
	win.where = where;
	win.what = what;
	win.lines = lines;
	win.section = section;
	win.scheme_statement = stmt;
    } else {
	var lines = countLines(what);
	var heightOffset = getHeightFactor();
	var win = window.open("html_scheme/emptyScheme.html",
			      "lines"+escape2+lines+
			      escape1+"where"+escape2+where+
			      escape1+"what"+escape2+what+
			      escape1+"section"+escape2+section+
			      escape1+"scheme_statement"+escape2+stmt,
			      "width=710"+
			      ",height="+((lines*getHeightFactor())+
					  getHeightOffset())+
			      ",scrollbars=yes");
    }
}


// get data from name of window; modified
// from JavaScript Definitive Guide, page 214
function getArgs(win) {
    var args = new Object();
    var query = win.name;
    var pairs = query.split(escape1);
    for (var i = 0; i < pairs.length; i++) {
	var pos = pairs[i].indexOf(escape2);
	if (pos == -1) continue;
	var argname = pairs[i].substring(0,pos);
	var value = pairs[i].substring(pos+1);
	args[argname] = value;
    }
    return args;
}

function generateJavaScriptContent() {
    // once we get to execute this on IE, document.all
    // is there. Do the following for IE, and do the
    // else part for all other browsers.
    if (document.all) {

	window.document.body.innerHTML =
	    'JavaScript expression from Section '+
	    window.section +
	    '; click "Eval" to evaluate it.' +
	    '<form name="form_'+window.where+'">' +
	    '<table>' +
	    '<tr>' +
	    '<td>' +
	    '<textarea name="source" rows="' +
	    (window.lines+1) +
	    '" cols="80">' +
	    window.what +
	    '</textarea>' +
	    '</td>' +
	    '</tr>' +
	    '<tr>' +
	    '<td>' +
	    '<input name="buttonJavaScript" type="button" value="Eval" onclick="evalJavaScript(\''+
	    window.where +
	    '\',document.form_'+window.where+'.source.value,true)">' +
	    '</input>' +
	    '</td>' +
	    '</tr>' +
	    '<tr>' +
	    '<td>' +
	    '<textarea readonly="true" name="resultJavaScript" rows="8" cols="80">' +
	    '</textarea>' +
	    '</td>' +
	    '</tr>' +
	    '<tr>' +
	    '<td>' +
	    '<textarea name="grammar" style="display:none;" rows="40" cols="120">' +
	    '</textarea>' +
	    '</td>' +
	    '</tr>' +
	    '<tr>' +
	    '<td>' +
	    '<input name="buttonGrammar" style="display:none;" type="button" value="Load Grammar" onclick="load_grammar(\'' + window.where + '\')"></input>' +
	    '</td>' +
	    '</tr>' +
	    '</table>' +
	    '</form>'
	    ;
    } else {
        window.latestConsole.display("other browsers: eval");
	// retrieve data from window name, a trick
	// to pass content data to the window.
	// (see comment on Opera under popupJavaScript)
	var args = getArgs(window);
	var section = args.section;
	var where = args.where;
	var what = args.what;
	var lines = parseInt(args.lines);

	window.javascript_statement = args.javascript_statement;

	window.document.body.innerHTML =
	    'JavaScript expression from Section '+
	    section +
	    '; click "Eval" to evaluate it.' +
	    '<form name="form_'+where+'">' +
	    '<table>' +
	    '<tr>' +
	    '<td>' +
	    '<textarea name="source" spellcheck="false" rows="' +
	    (lines+1) +
	    '" cols="80">' +
	    what +
	    '</textarea>' +
	    '</td>' +
	    '</tr>' +
	    '<tr>' +
	    '<td>' +
	    '<input name="buttonJavaScript" type="button" value="Eval" onclick="evalJavaScript(\''+
	    where +
	    '\',document.form_'+where+'.source.value,true)">' +
	    '</input>' +
	    '</td>' +
	    '</tr>' +
	    '<tr>' +
	    '<td>' +
	    '<textarea readonly="true" name="resultJavaScript" rows="8" cols="80">' +
	    '</textarea>' +
	    '</td>' +
	    '</tr>' +
	    '<tr>' +
	    '<td>' +
	    '<textarea name="grammar" style="display:none;" rows="40" cols="120">' +
	    '</textarea>' +
	    '</td>' +
	    '</tr>' +
	    '<tr>' +
	    '<td>' +
	    '<input name="buttonGrammar" style="display:none;" type="button" value="Load Grammar" onclick="load_grammar(\'' + where + '\')"></input>' +
	    '</td>' +
	    '</tr>' +
	    '</table>' +
	    '</form>'
	    ;
    }
}

// Note the trick to open an empty page first,
// and then have that page call generateJavaScriptContent().
// If the content is placed into innerHtml immediately,
// Firefox 2.0 will not display it.

// We pass relevant data in the name. This works in all browsers,
// whereas Opera does not preserve window attributes as in "win.lines = lines"

function popupJavaScript(where,what,section,stmt) {

    if (document.all) {

	var lines = countLines(what);
	var heightOffset = getHeightFactor();
	var win = window.open("emptyJavaScript.html", "Evaluator_"+where,
			      "width=710,height="+((lines*getHeightFactor())+getHeightOffset())+",scrollbars=yes");
	win.lines = lines;
	win.where = where;
	win.what = what;
	win.section = section;
	win.javascript_statement = stmt;
    } else {
	var lines = countLines(what);
	var heightOffset = getHeightFactor();
	var win = window.open("emptyJavaScript.html",
			      "lines"+escape2+lines+
			      escape1+"where"+escape2+where+
			      escape1+"what"+escape2+what+
			      escape1+"section"+escape2+section+
			      escape1+"javascript_statement"+escape2+stmt,
			      "width=710"+
			      ",height="+((lines*getHeightFactor())+
					  getHeightOffset())+
			      ",scrollbars=yes");
    }
}
;

function pair(x,xs) {
    return [x,xs];
}

function is_pair(x) {
    return x instanceof Array && x.length == 2;
}

function head(xs) {
    return xs[0];
}

function tail(xs) {
    return xs[1];
}

function is_list(xs) {
    return is_empty_list(xs) || (tail(xs) !== undefined && is_list(tail(xs)));
}

function list() {
    var the_list = [];
    for (var i = arguments.length - 1; i >= 0; i--)
	the_list = pair(arguments[i],the_list);
    return the_list;
}


function array_test(x) {
    if (this.Array.isArray === undefined) {
	return x instanceof Array;
    } else {
	return Array.isArray(x);
    }
}

function is_empty_list(xs) {
    if (array_test(xs)) {
        if  (xs.length === 0) {
            return true; }
        else if (xs.length === 2) {
            return false; }
        else {
	    return false;
        }
    } else {
	return false;
    }
}

function is_number(xs) {
    return typeof xs == "number";
}

function is_string(xs) {
    return typeof xs == "string";
}

function length(xs) {
    return  (is_empty_list(xs)) ? 0 : 1 + length(tail(xs));
}

function apply(f,xs) {
    var args = [];
    var len = length(xs);
    for (var i=0; i < len; i++) {
       args[i] = head(xs);
       xs = tail(xs);
    }
    return f.apply(f,args);
}

function map(f) {
   if (is_empty_list(arguments[1])) return [];
   else {
      var f = arguments[0];
      var f_args = [];
      var map_args = [f];
      for (var i=1; i < arguments.length; i++) {
          f_args[i-1] = head(arguments[i]);
          map_args[i] = tail(arguments[i]);
      }
      return pair(f.apply(f,f_args),map.apply(map,map_args));
   }
}

function display(x) {
    print(format(x));
}

function print(x) {
    window.latestConsole.display(x);
    return undefined;
}

function newline() { 
    print('');
    return;
}

function runtime() {
    var d = new Date();
    return d.getTime();
}

function error(x) {
    var output_string = x;
    for (var i=1; i < arguments.length; i++)
	output_string = output_string + " " + format(arguments[i]);
    alert(output_string);
    return 
}
;
/* Jison generated parser */

var parser = (function(){
var parser = {trace: function trace() { },
yy: {},
symbols_: {"error":2,"program":3,"statements":4,"EOF":5,"statement":6,"if":7,"(":8,"expression":9,")":10,"{":11,"}":12,"else":13,"function":14,"identifier":15,"identifiers":16,"var":17,"=":18,";":19,"return":20,"+":21,"-":22,"*":23,"/":24,"!":25,"%":26,"NUMBER":27,"true":28,"false":29,"DoubleQuoteString":30,"SingleQuoteString":31,"[]":32,"expressions":33,"nonemptyexpressions":34,",":35,"nonemptyidentifiers":36,"Identifier":37,"$accept":0,"$end":1},
terminals_: {2:"error",5:"EOF",7:"if",8:"(",10:")",11:"{",12:"}",13:"else",14:"function",17:"var",18:"=",19:";",20:"return",21:"+",22:"-",23:"*",24:"/",25:"!",26:"%",27:"NUMBER",28:"true",29:"false",30:"DoubleQuoteString",31:"SingleQuoteString",32:"[]",35:",",37:"Identifier"},
productions_: [0,[3,2],[4,0],[4,2],[6,11],[6,8],[6,5],[6,4],[6,2],[6,3],[9,3],[9,3],[9,3],[9,3],[9,2],[9,3],[9,2],[9,3],[9,1],[9,1],[9,1],[9,1],[9,1],[9,1],[9,1],[9,6],[9,4],[9,7],[33,1],[33,0],[34,3],[34,1],[16,1],[16,0],[36,3],[36,1],[15,1]],
performAction: function anonymous(yytext,yyleng,yylineno,yy,yystate,$$,_$) {

var $0 = $$.length - 1;
switch (yystate) {
case 1: return $$[$0-1]; 
break;
case 2: this.$ = []; 
break;
case 3: this.$ = pair($$[$0-1], $$[$0]); 
break;
case 4:
          this.$ = { tag: 'if', predicate: $$[$0-8], 
                 consequent: $$[$0-5], alternative: $$[$0-1] } ;
        
break;
case 5:
	  this.$ = { tag: 'var_definition', variable: $$[$0-6], 
                 value: { tag: 'function_definition',
                          parameters: $$[$0-4], 
                          body: $$[$0-1] } 
               };
        
break;
case 6:
	  this.$ = { tag: 'var_definition', variable: $$[$0-3], value: $$[$0-1] };
        
break;
case 7:
	  this.$ = { tag: 'assignment', variable: $$[$0-3], value: $$[$0-1] };
        
break;
case 8:this.$ = $$[$0-1];
break;
case 9:
           this.$ = { tag: 'return_statement', expression: $$[$0-1] };
        
break;
case 10:
           this.$ = { tag: 'application', 
                  operator: {tag:'variable', name: $$[$0-1]}, 
                  operands: [$$[$0-2],[$$[$0],[]]] 
                };
        
break;
case 11:
           this.$ = { tag: 'application', 
                  operator: {tag:'variable', name: $$[$0-1]}, 
                  operands: [$$[$0-2],[$$[$0],[]]] 
                };
        
break;
case 12:
           this.$ = { tag: 'application', 
                  operator: {tag:'variable', name: $$[$0-1]}, 
                  operands: [$$[$0-2],[$$[$0],[]]] 
                };
        
break;
case 13:
           this.$ = { tag: 'application', 
                  operator: {tag:'variable', name: $$[$0-1]}, 
                  operands: [$$[$0-2],[$$[$0],[]]] 
                };
        
break;
case 14:
           this.$ = { tag: 'application', 
                  operator: {tag:'variable', name: $$[$0-1]}, 
                  operands: [$$[$0],[]]
                };
        
break;
case 15:
           this.$ = { tag: 'application', 
                  operator: {tag:'variable', name: $$[$0-1]}, 
                  operands: [$$[$0-2],[$$[$0],[]]] 
                };
        
break;
case 16:
           this.$ = { tag: 'application', 
                  operator: {tag:'variable', name: $$[$0-1]}, 
                  operands: [$$[$0],[]] 
                };
        
break;
case 17:this.$ = $$[$0-1];
break;
case 18:this.$ = parseInt(yytext);
break;
case 19:this.$ = true;
break;
case 20:this.$ = false;
break;
case 21: this.$ = yytext.substring(1,yytext.length - 1).replace('\\"','"'); 
break;
case 22: this.$ = yytext.substring(1,yytext.length - 1).replace("\\'","'"); 
break;
case 23:this.$ = [];
break;
case 24:
           this.$ = { tag: 'variable', name: $$[$0] };
	
break;
case 25:
           this.$ = { tag: 'application', 
                  operator: $$[$0-4], operands: $$[$0-1] };
	
break;
case 26:
           this.$ = { tag: 'application', 
                  operator: { tag: 'variable', name: $$[$0-3] }, 
		  operands: $$[$0-1] };
	
break;
case 27:
	   this.$ = { tag: 'function_definition', 
                  parameters: $$[$0-4], body: $$[$0-1]};
        
break;
case 28: this.$ = $$[$0]; 
break;
case 29: this.$ = []; 
break;
case 30: this.$ = [ $$[$0-2], $$[$0] ]; 
break;
case 31: this.$ = [ $$[$0], [] ]; 
break;
case 32: this.$ = $$[$0]; 
break;
case 33: this.$ = []; 
break;
case 34: this.$ = [ $$[$0-2], $$[$0] ]; 
break;
case 35: this.$ = [ $$[$0], [] ]; 
break;
case 36:this.$ = yytext;
break;
}
},
table: [{3:1,4:2,5:[2,2],6:3,7:[1,4],8:[1,13],9:8,14:[1,5],15:7,17:[1,6],20:[1,9],22:[1,12],25:[1,11],27:[1,14],28:[1,15],29:[1,16],30:[1,17],31:[1,18],32:[1,19],37:[1,10]},{1:[3]},{5:[1,20]},{4:21,5:[2,2],6:3,7:[1,4],8:[1,13],9:8,12:[2,2],14:[1,5],15:7,17:[1,6],20:[1,9],22:[1,12],25:[1,11],27:[1,14],28:[1,15],29:[1,16],30:[1,17],31:[1,18],32:[1,19],37:[1,10]},{8:[1,22]},{8:[1,24],15:23,37:[1,10]},{15:25,37:[1,10]},{8:[1,27],18:[1,26],19:[2,24],21:[2,24],22:[2,24],23:[2,24],24:[2,24],26:[2,24]},{19:[1,28],21:[1,29],22:[1,30],23:[1,31],24:[1,32],26:[1,33]},{8:[1,13],9:34,14:[1,36],15:35,22:[1,12],25:[1,11],27:[1,14],28:[1,15],29:[1,16],30:[1,17],31:[1,18],32:[1,19],37:[1,10]},{8:[2,36],10:[2,36],18:[2,36],19:[2,36],21:[2,36],22:[2,36],23:[2,36],24:[2,36],26:[2,36],35:[2,36]},{8:[1,13],9:37,14:[1,36],15:35,22:[1,12],25:[1,11],27:[1,14],28:[1,15],29:[1,16],30:[1,17],31:[1,18],32:[1,19],37:[1,10]},{8:[1,13],9:38,14:[1,36],15:35,22:[1,12],25:[1,11],27:[1,14],28:[1,15],29:[1,16],30:[1,17],31:[1,18],32:[1,19],37:[1,10]},{8:[1,13],9:39,14:[1,36],15:35,22:[1,12],25:[1,11],27:[1,14],28:[1,15],29:[1,16],30:[1,17],31:[1,18],32:[1,19],37:[1,10]},{10:[2,18],19:[2,18],21:[2,18],22:[2,18],23:[2,18],24:[2,18],26:[2,18],35:[2,18]},{10:[2,19],19:[2,19],21:[2,19],22:[2,19],23:[2,19],24:[2,19],26:[2,19],35:[2,19]},{10:[2,20],19:[2,20],21:[2,20],22:[2,20],23:[2,20],24:[2,20],26:[2,20],35:[2,20]},{10:[2,21],19:[2,21],21:[2,21],22:[2,21],23:[2,21],24:[2,21],26:[2,21],35:[2,21]},{10:[2,22],19:[2,22],21:[2,22],22:[2,22],23:[2,22],24:[2,22],26:[2,22],35:[2,22]},{10:[2,23],19:[2,23],21:[2,23],22:[2,23],23:[2,23],24:[2,23],26:[2,23],35:[2,23]},{1:[2,1]},{5:[2,3],12:[2,3]},{8:[1,13],9:40,14:[1,36],15:35,22:[1,12],25:[1,11],27:[1,14],28:[1,15],29:[1,16],30:[1,17],31:[1,18],32:[1,19],37:[1,10]},{8:[1,41]},{10:[2,33],15:44,16:42,36:43,37:[1,10]},{18:[1,45]},{8:[1,13],9:46,14:[1,36],15:35,22:[1,12],25:[1,11],27:[1,14],28:[1,15],29:[1,16],30:[1,17],31:[1,18],32:[1,19],37:[1,10]},{8:[1,13],9:49,10:[2,29],14:[1,36],15:35,22:[1,12],25:[1,11],27:[1,14],28:[1,15],29:[1,16],30:[1,17],31:[1,18],32:[1,19],33:47,34:48,37:[1,10]},{5:[2,8],7:[2,8],8:[2,8],12:[2,8],14:[2,8],17:[2,8],20:[2,8],22:[2,8],25:[2,8],27:[2,8],28:[2,8],29:[2,8],30:[2,8],31:[2,8],32:[2,8],37:[2,8]},{8:[1,13],9:50,14:[1,36],15:35,22:[1,12],25:[1,11],27:[1,14],28:[1,15],29:[1,16],30:[1,17],31:[1,18],32:[1,19],37:[1,10]},{8:[1,13],9:51,14:[1,36],15:35,22:[1,12],25:[1,11],27:[1,14],28:[1,15],29:[1,16],30:[1,17],31:[1,18],32:[1,19],37:[1,10]},{8:[1,13],9:52,14:[1,36],15:35,22:[1,12],25:[1,11],27:[1,14],28:[1,15],29:[1,16],30:[1,17],31:[1,18],32:[1,19],37:[1,10]},{8:[1,13],9:53,14:[1,36],15:35,22:[1,12],25:[1,11],27:[1,14],28:[1,15],29:[1,16],30:[1,17],31:[1,18],32:[1,19],37:[1,10]},{8:[1,13],9:54,14:[1,36],15:35,22:[1,12],25:[1,11],27:[1,14],28:[1,15],29:[1,16],30:[1,17],31:[1,18],32:[1,19],37:[1,10]},{19:[1,55],21:[1,29],22:[1,30],23:[1,31],24:[1,32],26:[1,33]},{8:[1,27],10:[2,24],19:[2,24],21:[2,24],22:[2,24],23:[2,24],24:[2,24],26:[2,24],35:[2,24]},{8:[1,24]},{10:[2,14],19:[2,14],21:[2,14],22:[2,14],23:[2,14],24:[2,14],26:[2,14],35:[2,14]},{10:[2,16],19:[2,16],21:[2,16],22:[2,16],23:[2,16],24:[2,16],26:[2,16],35:[2,16]},{10:[1,56],21:[1,29],22:[1,30],23:[1,31],24:[1,32],26:[1,33]},{10:[1,57],21:[1,29],22:[1,30],23:[1,31],24:[1,32],26:[1,33]},{10:[2,33],15:44,16:58,36:43,37:[1,10]},{10:[1,59]},{10:[2,32]},{10:[2,35],35:[1,60]},{8:[1,13],9:61,14:[1,36],15:35,22:[1,12],25:[1,11],27:[1,14],28:[1,15],29:[1,16],30:[1,17],31:[1,18],32:[1,19],37:[1,10]},{19:[1,62],21:[1,29],22:[1,30],23:[1,31],24:[1,32],26:[1,33]},{10:[1,63]},{10:[2,28]},{10:[2,31],21:[1,29],22:[1,30],23:[1,31],24:[1,32],26:[1,33],35:[1,64]},{10:[2,10],19:[2,10],21:[2,10],22:[2,10],23:[1,31],24:[1,32],26:[1,33],35:[2,10]},{10:[2,11],19:[2,11],21:[2,11],22:[2,11],23:[1,31],24:[1,32],26:[1,33],35:[2,11]},{10:[2,12],19:[2,12],21:[2,12],22:[2,12],23:[2,12],24:[2,12],26:[2,12],35:[2,12]},{10:[2,13],19:[2,13],21:[2,13],22:[2,13],23:[2,13],24:[2,13],26:[2,13],35:[2,13]},{10:[2,15],19:[2,15],21:[2,15],22:[2,15],23:[2,15],24:[2,15],26:[2,15],35:[2,15]},{5:[2,9],7:[2,9],8:[2,9],12:[2,9],14:[2,9],17:[2,9],20:[2,9],22:[2,9],25:[2,9],27:[2,9],28:[2,9],29:[2,9],30:[2,9],31:[2,9],32:[2,9],37:[2,9]},{8:[1,65],10:[2,17],19:[2,17],21:[2,17],22:[2,17],23:[2,17],24:[2,17],26:[2,17],35:[2,17]},{11:[1,66]},{10:[1,67]},{11:[1,68]},{15:44,36:69,37:[1,10]},{19:[1,70],21:[1,29],22:[1,30],23:[1,31],24:[1,32],26:[1,33]},{5:[2,7],7:[2,7],8:[2,7],12:[2,7],14:[2,7],17:[2,7],20:[2,7],22:[2,7],25:[2,7],27:[2,7],28:[2,7],29:[2,7],30:[2,7],31:[2,7],32:[2,7],37:[2,7]},{10:[2,26],19:[2,26],21:[2,26],22:[2,26],23:[2,26],24:[2,26],26:[2,26],35:[2,26]},{8:[1,13],9:49,14:[1,36],15:35,22:[1,12],25:[1,11],27:[1,14],28:[1,15],29:[1,16],30:[1,17],31:[1,18],32:[1,19],34:71,37:[1,10]},{8:[1,13],9:49,10:[2,29],14:[1,36],15:35,22:[1,12],25:[1,11],27:[1,14],28:[1,15],29:[1,16],30:[1,17],31:[1,18],32:[1,19],33:72,34:48,37:[1,10]},{4:73,6:3,7:[1,4],8:[1,13],9:8,12:[2,2],14:[1,5],15:7,17:[1,6],20:[1,9],22:[1,12],25:[1,11],27:[1,14],28:[1,15],29:[1,16],30:[1,17],31:[1,18],32:[1,19],37:[1,10]},{11:[1,74]},{4:75,6:3,7:[1,4],8:[1,13],9:8,12:[2,2],14:[1,5],15:7,17:[1,6],20:[1,9],22:[1,12],25:[1,11],27:[1,14],28:[1,15],29:[1,16],30:[1,17],31:[1,18],32:[1,19],37:[1,10]},{10:[2,34]},{5:[2,6],7:[2,6],8:[2,6],12:[2,6],14:[2,6],17:[2,6],20:[2,6],22:[2,6],25:[2,6],27:[2,6],28:[2,6],29:[2,6],30:[2,6],31:[2,6],32:[2,6],37:[2,6]},{10:[2,30]},{10:[1,76]},{12:[1,77]},{4:78,6:3,7:[1,4],8:[1,13],9:8,12:[2,2],14:[1,5],15:7,17:[1,6],20:[1,9],22:[1,12],25:[1,11],27:[1,14],28:[1,15],29:[1,16],30:[1,17],31:[1,18],32:[1,19],37:[1,10]},{12:[1,79]},{10:[2,25],19:[2,25],21:[2,25],22:[2,25],23:[2,25],24:[2,25],26:[2,25],35:[2,25]},{13:[1,80]},{12:[1,81]},{10:[2,27],19:[2,27],21:[2,27],22:[2,27],23:[2,27],24:[2,27],26:[2,27],35:[2,27]},{11:[1,82]},{5:[2,5],7:[2,5],8:[2,5],12:[2,5],14:[2,5],17:[2,5],20:[2,5],22:[2,5],25:[2,5],27:[2,5],28:[2,5],29:[2,5],30:[2,5],31:[2,5],32:[2,5],37:[2,5]},{4:83,6:3,7:[1,4],8:[1,13],9:8,12:[2,2],14:[1,5],15:7,17:[1,6],20:[1,9],22:[1,12],25:[1,11],27:[1,14],28:[1,15],29:[1,16],30:[1,17],31:[1,18],32:[1,19],37:[1,10]},{12:[1,84]},{5:[2,4],7:[2,4],8:[2,4],12:[2,4],14:[2,4],17:[2,4],20:[2,4],22:[2,4],25:[2,4],27:[2,4],28:[2,4],29:[2,4],30:[2,4],31:[2,4],32:[2,4],37:[2,4]}],
defaultActions: {20:[2,1],43:[2,32],48:[2,28],69:[2,34],71:[2,30]},
parseError: function parseError(str, hash) {
    throw new Error(str);
},
parse: function parse(input) {
    var self = this, stack = [0], vstack = [null], lstack = [], table = this.table, yytext = "", yylineno = 0, yyleng = 0, recovering = 0, TERROR = 2, EOF = 1;
    this.lexer.setInput(input);
    this.lexer.yy = this.yy;
    this.yy.lexer = this.lexer;
    this.yy.parser = this;
    if (typeof this.lexer.yylloc == "undefined")
        this.lexer.yylloc = {};
    var yyloc = this.lexer.yylloc;
    lstack.push(yyloc);
    var ranges = this.lexer.options && this.lexer.options.ranges;
    if (typeof this.yy.parseError === "function")
        this.parseError = this.yy.parseError;
    function popStack(n) {
        stack.length = stack.length - 2 * n;
        vstack.length = vstack.length - n;
        lstack.length = lstack.length - n;
    }
    function lex() {
        var token;
        token = self.lexer.lex() || 1;
        if (typeof token !== "number") {
            token = self.symbols_[token] || token;
        }
        return token;
    }
    var symbol, preErrorSymbol, state, action, a, r, yyval = {}, p, len, newState, expected;
    while (true) {
        state = stack[stack.length - 1];
        if (this.defaultActions[state]) {
            action = this.defaultActions[state];
        } else {
            if (symbol === null || typeof symbol == "undefined") {
                symbol = lex();
            }
            action = table[state] && table[state][symbol];
        }
        if (typeof action === "undefined" || !action.length || !action[0]) {
            var errStr = "";
            if (!recovering) {
                expected = [];
                for (p in table[state])
                    if (this.terminals_[p] && p > 2) {
                        expected.push("'" + this.terminals_[p] + "'");
                    }
                if (this.lexer.showPosition) {
                    errStr = "Parse error on line " + (yylineno + 1) + ":\n" + this.lexer.showPosition() + "\nExpecting " + expected.join(", ") + ", got '" + (this.terminals_[symbol] || symbol) + "'";
                } else {
                    errStr = "Parse error on line " + (yylineno + 1) + ": Unexpected " + (symbol == 1?"end of input":"'" + (this.terminals_[symbol] || symbol) + "'");
                }
                this.parseError(errStr, {text: this.lexer.match, token: this.terminals_[symbol] || symbol, line: this.lexer.yylineno, loc: yyloc, expected: expected});
            }
        }
        if (action[0] instanceof Array && action.length > 1) {
            throw new Error("Parse Error: multiple actions possible at state: " + state + ", token: " + symbol);
        }
        switch (action[0]) {
        case 1:
            stack.push(symbol);
            vstack.push(this.lexer.yytext);
            lstack.push(this.lexer.yylloc);
            stack.push(action[1]);
            symbol = null;
            if (!preErrorSymbol) {
                yyleng = this.lexer.yyleng;
                yytext = this.lexer.yytext;
                yylineno = this.lexer.yylineno;
                yyloc = this.lexer.yylloc;
                if (recovering > 0)
                    recovering--;
            } else {
                symbol = preErrorSymbol;
                preErrorSymbol = null;
            }
            break;
        case 2:
            len = this.productions_[action[1]][1];
            yyval.$ = vstack[vstack.length - len];
            yyval._$ = {first_line: lstack[lstack.length - (len || 1)].first_line, last_line: lstack[lstack.length - 1].last_line, first_column: lstack[lstack.length - (len || 1)].first_column, last_column: lstack[lstack.length - 1].last_column};
            if (ranges) {
                yyval._$.range = [lstack[lstack.length - (len || 1)].range[0], lstack[lstack.length - 1].range[1]];
            }
            r = this.performAction.call(yyval, yytext, yyleng, yylineno, this.yy, action[1], vstack, lstack);
            if (typeof r !== "undefined") {
                return r;
            }
            if (len) {
                stack = stack.slice(0, -1 * len * 2);
                vstack = vstack.slice(0, -1 * len);
                lstack = lstack.slice(0, -1 * len);
            }
            stack.push(this.productions_[action[1]][0]);
            vstack.push(yyval.$);
            lstack.push(yyval._$);
            newState = table[stack[stack.length - 2]][stack[stack.length - 1]];
            stack.push(newState);
            break;
        case 3:
            return true;
        }
    }
    return true;
}
};
/* Jison generated lexer */
var lexer = (function(){
var lexer = ({EOF:1,
parseError:function parseError(str, hash) {
        if (this.yy.parser) {
            this.yy.parser.parseError(str, hash);
        } else {
            throw new Error(str);
        }
    },
setInput:function (input) {
        this._input = input;
        this._more = this._less = this.done = false;
        this.yylineno = this.yyleng = 0;
        this.yytext = this.matched = this.match = '';
        this.conditionStack = ['INITIAL'];
        this.yylloc = {first_line:1,first_column:0,last_line:1,last_column:0};
        if (this.options.ranges) this.yylloc.range = [0,0];
        this.offset = 0;
        return this;
    },
input:function () {
        var ch = this._input[0];
        this.yytext += ch;
        this.yyleng++;
        this.offset++;
        this.match += ch;
        this.matched += ch;
        var lines = ch.match(/(?:\r\n?|\n).*/g);
        if (lines) {
            this.yylineno++;
            this.yylloc.last_line++;
        } else {
            this.yylloc.last_column++;
        }
        if (this.options.ranges) this.yylloc.range[1]++;

        this._input = this._input.slice(1);
        return ch;
    },
unput:function (ch) {
        var len = ch.length;
        var lines = ch.split(/(?:\r\n?|\n)/g);

        this._input = ch + this._input;
        this.yytext = this.yytext.substr(0, this.yytext.length-len-1);
        //this.yyleng -= len;
        this.offset -= len;
        var oldLines = this.match.split(/(?:\r\n?|\n)/g);
        this.match = this.match.substr(0, this.match.length-1);
        this.matched = this.matched.substr(0, this.matched.length-1);

        if (lines.length-1) this.yylineno -= lines.length-1;
        var r = this.yylloc.range;

        this.yylloc = {first_line: this.yylloc.first_line,
          last_line: this.yylineno+1,
          first_column: this.yylloc.first_column,
          last_column: lines ?
              (lines.length === oldLines.length ? this.yylloc.first_column : 0) + oldLines[oldLines.length - lines.length].length - lines[0].length:
              this.yylloc.first_column - len
          };

        if (this.options.ranges) {
            this.yylloc.range = [r[0], r[0] + this.yyleng - len];
        }
        return this;
    },
more:function () {
        this._more = true;
        return this;
    },
less:function (n) {
        this.unput(this.match.slice(n));
    },
pastInput:function () {
        var past = this.matched.substr(0, this.matched.length - this.match.length);
        return (past.length > 20 ? '...':'') + past.substr(-20).replace(/\n/g, "");
    },
upcomingInput:function () {
        var next = this.match;
        if (next.length < 20) {
            next += this._input.substr(0, 20-next.length);
        }
        return (next.substr(0,20)+(next.length > 20 ? '...':'')).replace(/\n/g, "");
    },
showPosition:function () {
        var pre = this.pastInput();
        var c = new Array(pre.length + 1).join("-");
        return pre + this.upcomingInput() + "\n" + c+"^";
    },
next:function () {
        if (this.done) {
            return this.EOF;
        }
        if (!this._input) this.done = true;

        var token,
            match,
            tempMatch,
            index,
            col,
            lines;
        if (!this._more) {
            this.yytext = '';
            this.match = '';
        }
        var rules = this._currentRules();
        for (var i=0;i < rules.length; i++) {
            tempMatch = this._input.match(this.rules[rules[i]]);
            if (tempMatch && (!match || tempMatch[0].length > match[0].length)) {
                match = tempMatch;
                index = i;
                if (!this.options.flex) break;
            }
        }
        if (match) {
            lines = match[0].match(/(?:\r\n?|\n).*/g);
            if (lines) this.yylineno += lines.length;
            this.yylloc = {first_line: this.yylloc.last_line,
                           last_line: this.yylineno+1,
                           first_column: this.yylloc.last_column,
                           last_column: lines ? lines[lines.length-1].length-lines[lines.length-1].match(/\r?\n?/)[0].length : this.yylloc.last_column + match[0].length};
            this.yytext += match[0];
            this.match += match[0];
            this.matches = match;
            this.yyleng = this.yytext.length;
            if (this.options.ranges) {
                this.yylloc.range = [this.offset, this.offset += this.yyleng];
            }
            this._more = false;
            this._input = this._input.slice(match[0].length);
            this.matched += match[0];
            token = this.performAction.call(this, this.yy, this, rules[index],this.conditionStack[this.conditionStack.length-1]);
            if (this.done && this._input) this.done = false;
            if (token) return token;
            else return;
        }
        if (this._input === "") {
            return this.EOF;
        } else {
            return this.parseError('Lexical error on line '+(this.yylineno+1)+'. Unrecognized text.\n'+this.showPosition(),
                    {text: "", token: null, line: this.yylineno});
        }
    },
lex:function lex() {
        var r = this.next();
        if (typeof r !== 'undefined') {
            return r;
        } else {
            return this.lex();
        }
    },
begin:function begin(condition) {
        this.conditionStack.push(condition);
    },
popState:function popState() {
        return this.conditionStack.pop();
    },
_currentRules:function _currentRules() {
        return this.conditions[this.conditionStack[this.conditionStack.length-1]].rules;
    },
topState:function () {
        return this.conditionStack[this.conditionStack.length-2];
    },
pushState:function begin(condition) {
        this.begin(condition);
    }});
lexer.options = {};
lexer.performAction = function anonymous(yy,yy_,$avoiding_name_collisions,YY_START) {

var YYSTATE=YY_START
switch($avoiding_name_collisions) {
case 0:/* skip whitespace */
break;
case 1:return 14
break;
case 2:return 20
break;
case 3:return 7
break;
case 4:return 'new'
break;
case 5:return 13
break;
case 6:return 17
break;
case 7:return 18
break;
case 8:return 11
break;
case 9:return 12
break;
case 10:return 19
break;
case 11:return 35
break;
case 12:return 28
break;
case 13:return 29
break;
case 14:return 30;
break;
case 15:return 31;
break;
case 16:return 37
break;
case 17:return 27
break;
case 18:return 32
break;
case 19:return 23
break;
case 20:return 24
break;
case 21:return 22
break;
case 22:return 21
break;
case 23:return 25
break;
case 24:return 26
break;
case 25:return 26
break;
case 26:return 26
break;
case 27:return '>'
break;
case 28:return '<'
break;
case 29:return '>='
break;
case 30:return '<='
break;
case 31:return '&&'
break;
case 32:return '||'
break;
case 33:return 8
break;
case 34:return 10
break;
case 35:return 5
break;
case 36:return 'INVALID'
break;
}
};
lexer.rules = [/^(?:\s+)/,/^(?:function\b)/,/^(?:return\b)/,/^(?:if\b)/,/^(?:new\b)/,/^(?:else\b)/,/^(?:var\b)/,/^(?:=)/,/^(?:\{)/,/^(?:\})/,/^(?:;)/,/^(?:,)/,/^(?:true\b)/,/^(?:false\b)/,/^(?:"(\\"|[^\"])*")/,/^(?:'(\\'|[^\'])*')/,/^(?:[A-Za-z_][A-Za-z0-9_]*)/,/^(?:[0-9]+(\.[0-9]+)?\b)/,/^(?:\[\])/,/^(?:\*)/,/^(?:\/)/,/^(?:-)/,/^(?:\+)/,/^(?:!)/,/^(?:%)/,/^(?:===)/,/^(?:!==)/,/^(?:>)/,/^(?:<)/,/^(?:>=)/,/^(?:<=)/,/^(?:&&)/,/^(?:\|\|)/,/^(?:\()/,/^(?:\))/,/^(?:$)/,/^(?:.)/];
lexer.conditions = {"INITIAL":{"rules":[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36],"inclusive":true}};
return lexer;})()
parser.lexer = lexer;
function Parser () { this.yy = {}; }Parser.prototype = parser;parser.Parser = Parser;
return new Parser;
})();
if (typeof require !== 'undefined' && typeof exports !== 'undefined') {
exports.parser = parser;
exports.Parser = parser.Parser;
exports.parse = function () { return parser.parse.apply(parser, arguments); }
exports.main = function commonjsMain(args) {
    if (!args[1])
        throw new Error('Usage: '+args[0]+' FILE');
    var source, cwd;
    if (typeof process !== 'undefined') {
        source = require('fs').readFileSync(require('path').resolve(args[1]), "utf8");
    } else {
        source = require("file").path(require("file").cwd()).join(args[1]).read({charset: "utf-8"});
    }
    return exports.parser.parse(source);
}
if (typeof module !== 'undefined' && require.main === module) {
  exports.main(typeof process !== 'undefined' ? process.argv.slice(1) : require("system").args);
}
}
;
function m(t,d) {
 // window.navigate("mailto:"+t+"@"+d);
  window.location="mailto:"+t+"@"+d;
}

function R(s) {
  s='var e=TopEnv;'+s;
  s=eval(s);
}

//

var trace = false;

function clone(x) {
  var i, r = new x.constructor;
  for(i in x) {
    if( x[i] != x.constructor.prototype[i] )
      r[i] = x[i];
  }
  return r;
}

//
// Classes...
//

// Pair - List construction block

function Pair( car, cdr ) {
  this.car = car;
  this.cdr = cdr;
}

function isNil(x) {
  return x == theNil || x == null || ( (x instanceof Pair) &&
         x.car == null && x.cdr == null );
}

function Nil() { }
var theNil = new Nil();

Nil.prototype.Str = function() { return '()'; }
Nil.prototype.Html = dumbHtml;
Nil.prototype.ListCopy = function() { return this; }

// Char class constructor - since we don't have Char type in JS
// 2Do: Chat = String with .isChar=true ??

function Char(c) {
  Chars[ this.value = c ] = this;
}

// Symbol class constructor - to distinguish it from String

function Symbol(s) {
  Symbols[ this.name = s ] = this;
}

var Symbols = new Object();
var Chars = new Object();

function getSymbol(name,leaveCase) {
  if( ! leaveCase ) name = name.toLowerCase(); // case-insensitive symbols!
  if( Symbols[name] != undefined ) {
    return Symbols[name];
  }
  return new Symbol(name);
}

function getChar(c) {
  if( Chars[c] != undefined ) {
    return Chars[c];
  }
  return new Char(c);
}

//
// Parser
//

// Tokenizer

function tokenize(txt) {
  var tokens = new Array(), oldTxt=null;
  while( txt != "" && oldTxt != txt ) {
    oldTxt = txt;
    txt = txt.replace( /^\s*(;[^\r\n]*(\r|\n|$)|#\\[^\w]|#?(\(|\[|{)|\)|\]|}|\'|`|,@|,|\"(\\(.|$)|[^\"\\])*(\"|$)|[^\s()\[\]{}]+)/,
      function($0,$1) {
        if( $1.charAt(0) != ';' ) tokens[tokens.length]=$1;
        return "";
      } );
  }
  return tokens;
}

// Parser class constructor

function Parser(txt) {
  this.tokens = tokenize(txt);
  this.i = 0;
}

// get list items until ')'

Parser.prototype.getList = function( close ) {
  var list = theNil, prev = list;
  while( this.i < this.tokens.length ) {
    if( this.tokens[ this.i ] == ')' ||
        this.tokens[ this.i ] == ']' ||
        this.tokens[ this.i ] == '}' ) {
      this.i++; break;
    }

    if( this.tokens[ this.i ] == '.' ) {
      this.i++;
      var o = this.getObject();
      if( o != null && list != theNil ) {
        prev.cdr = o;
      }
    } else {
      var cur = new Pair( this.getObject(), theNil );
      if( list == theNil ) list = cur;
      else prev.cdr = cur;
      prev = cur;
    }
  }
  return list;
}

Parser.prototype.getVector = function( close ) {
  var arr = new Array();
  while( this.i < this.tokens.length ) {
    if( this.tokens[ this.i ] == ')' ||
        this.tokens[ this.i ] == ']' ||
        this.tokens[ this.i ] == '}' ) { this.i++; break; }
    arr[ arr.length ] = this.getObject();
  }
  return arr;
}

// get object

Parser.prototype.getObject = function() {
  if( this.i >= this.tokens.length ) return null;
  var t = this.tokens[ this.i++ ];

 // if( t == ')' ) return null;

  var s = t == "'" ? 'quote' :
          t == "`" ? 'quasiquote' :
          t == "," ? 'unquote' :
          t == ",@" ? 'unquote-splicing' : false;
  if( s || t == '(' || t == '#(' ||
           t == '[' || t == '#[' ||
           t == '{' || t == '#{' ) {
    return s ? new Pair( getSymbol(s),
               new Pair( this.getObject(),
               theNil ))
             : (t=='(' || t=='[' || t=='{') ? this.getList(t) : this.getVector(t);
  } else {

    var n;
    if( /^#x[0-9a-z]+$/i.test(t) ) {  // #x... Hex
      n = new Number('0x'+t.substring(2,t.length) );
    } else if( /^#d[0-9\.]+$/i.test(t) ) {  // #d... Decimal
      n = new Number( t.substring(2,t.length) );
    } else n = new Number(t);  // use constrictor as parser

    if( ! isNaN(n) ) {
      return n.valueOf();
    } else if( t == '#f' || t == '#F' ) {
      return false;
    } else if( t == '#t' || t == '#T' ) {
      return true;
    } else if( t.toLowerCase() == '#\\newline' ) {
      return getChar('\n');
    } else if( t.toLowerCase() == '#\\space' ) {
      return getChar(' ');
    } else if( /^#\\.$/.test(t) ) {
      return getChar( t.charAt(2) );
    } else if( /^\"(\\(.|$)|[^\"\\])*\"?$/.test(t) ) {
       return t.replace( /^\"|\\(.|$)|\"$/g, function($0,$1) {
           return $1 ? $1 : '';
         } );
    } else return getSymbol(t);  // 2Do: validate !!
  }
}

//
// Printers
//

Boolean.prototype.Str = function () {
  return this.valueOf() ? '#t' : '#f';
}

Char.prototype.Str = function () {
  if( this.value == ' ' ) return '#\\space';
  if( this.value == '\n' ) return '#\\newline';
  return '#\\'+this.value;
}

Number.prototype.Str = function () {
  return this.toString();
}

Pair.prototype.Str = function () {
  var s = '';
  for( var o = this; o != null && o instanceof Pair && (o.car != null || o.cdr != null); o = o.cdr ) {
    if( o.car != null ) {
      if(s) s += ' ';
      s += Str(o.car);
    }
  }
  if( o != theNil && o != null && !( o instanceof Pair ) )
    s += ' . ' + Str(o);
  return '('+s+')';
}

String.prototype.Str = function () {
  return '"'+this.replace(/\\|\"/g,function($0){return'\\'+$0;})+'"';
}

Symbol.prototype.Str = function () {
  return this.name;
}

Function.prototype.Str = function () {
  return '#primitive' + (trace ? '<'+this+'>' : '');
}

function Str(obj) {
  if( obj == null ) return "#null";
  if( obj.Str ) return obj.Str();
  var c = obj.constructor, r;
  if( c ) {
    if( r = /^\s*function\s+(\w+)\(/.exec(c) ) c = r[1];
    return '#obj<'+c+'>';
  }
  return '#<'+obj+'>';
}

function Html(obj) {
  if( obj == null ) return "#null";
  if( obj.Html ) return obj.Html();
  return escapeHTML( '#obj<'+obj+'>' );
}

Array.prototype.Str = function () {
  var s='',i;
  for( i=0; i<this.length; i++ ) {
    if( s != '' ) s += ' ';
    s += Str( this[i] );
  }
  return '#('+s+')';
}

Continuation.prototype.Str = function () {
  return "#continuation";
}

// HTML output

function escapeHTML(s) {
  return s.replace( /(&)|(<)|(>)/g,
    function($0,$1,$2,$3) {
      return $1 ? '&amp;' : $2 ? '&lt;' : '&gt;';
    } );
}

function dumbHtml() {
  return escapeHTML( this.Str() );
}

function pairHtml() {
  var s1='',s2='', i, cells = new Array(), allSimple=true, firstSymbol=false;
  for( var o = this; o instanceof Pair && !isNil(o); o = o.cdr ) {
    if( o.car != null ) {
      if( cells.length == 0 )
        firstSymbol = o.car instanceof Symbol && o.car != theBegin;
      allSimple = allSimple && !(o.car instanceof Pair) &&
                               !(o.car instanceof Array);
      cells[cells.length] = Html(o.car);
    }
  }
  if( o != theNil && o != null && !( o instanceof Pair ) ) {
    cells[cells.length] = '.';
    allSimple = allSimple && !(o instanceof Array);
    cells[cells.length] = Html(o);
    if( firstSymbol && cells.length == 3 ) allSimple = true;
  }

  var rowSpan = allSimple ? 1 : firstSymbol ? cells.length-1 : cells.length;
  rowSpan = rowSpan>1 ? ' rowSpan='+rowSpan : '';

  var edit = ''; // " onClick=editCell()"
  for( i=0; i<cells.length; i++ ) {
    if( allSimple || i<1 || (i<2 && firstSymbol) ) {
      s1 += "<td"+(cells[i]=='.'?'':edit)
         + (i==0&&firstSymbol ? ' valign=top'+rowSpan : '')
         + ">" + cells[i] + "<\/td>";
    } else {
      s2 += "<tr><td"+(cells[i]=='.'?'':edit)
         + ">" + cells[i] + "<\/td><\/tr>";
    }
  }

  return '<table border=0 cellspacing=1 cellpadding=4>'
       + '<tr><td valign=top'+rowSpan+'>(<\/td>'
       + s1 + '<td valign=bottom'+rowSpan+'>)<\/td><\/tr>' + s2 + '<\/table>';
//  onClick=hv(this)
}

Boolean.prototype.Html = dumbHtml;
Char.prototype.Html = dumbHtml;
Number.prototype.Html = dumbHtml;
Pair.prototype.Html = pairHtml;
String.prototype.Html = dumbHtml;
Symbol.prototype.Html = dumbHtml;
Function.prototype.Html = dumbHtml;
Array.prototype.Html = dumbHtml;
Continuation.prototype.Html = dumbHtml;

//
// Environment
//

function Env(parent) {
  this.parentEnv = parent;
}

Env.prototype.get = function(name) {
  var v = this[name]; if( v != undefined ) return v;
  for( var o = this.parentEnv; o; o = o.parentEnv ) {
    v = o[name]; if( v != undefined ) return v;
  }
 // if( typeof(v) == 'undefined' ) {
 //   if( this.parentEnv ) return this.parentEnv.get(name); else
    throw new Ex("unbound symbol "+name);
 // } else return v;
}

Env.prototype.set = function( name, value ) {
  for( var o=this; o; o=o.parentEnv )
    if( o[name] != undefined ) return o[name]=value;
 // if( typeof(this[name]) == 'undefined' ) {
 //   if( this.parentEnv ) this.parentEnv.set(name,value); else
    throw new Ex("cannot set! unbound symbol "+name);
 // } else this[name] = value;
}

Env.prototype.Str = function() {
  var s = '',i;
  for( i in this ) {
    if( ! Env.prototype[i] && this[i]!=TopEnv ) {
      if( s != '' ) s += ',';
      var v = this[i];
      s += i + '=' + ( v instanceof Lambda ? '#lambda' :
                       typeof(v) == 'function' ? '#js' :
                       v ? v.Str() : v );
    }
  }
  return '['+s+']';
}

Env.prototype.With = function(a,v) { this[a]=v; this.Private=true; return this; }

// Top Environment

var TopEnv = new Env();

//

function Lambda(args,body,env,compiled) {
  this.args = args;
  this.body = body;
  this.env = env;
  this.compiled = compiled;
}

Lambda.prototype.clone = function(e) {
  if( this.env.Private ) {
    e = new Env(e);
    var i; for( i in this.env ) if(e[i]==undefined) e[i]=this.env[i];
  }

  return new Lambda( this.args, this.body, e, this.compiled);
}

Lambda.prototype.Html = dumbHtml;

Lambda.prototype.Str = function() {
  return "#lambda" + (trace ? "<"+this.args.Str()
        + ',' + this.body.Str()
       // + ( trace ? ',' + this.env.Str() : '' )
        + ">" : '');
}

//
// Evaluator - new state engine (for tail/rec and call/cc)
//

function State(obj,env,cc) {
  this.obj = obj;
  this.env = env;
  this.cc = cc;
}

function stateEval(noTrace) {
  if( this.obj == null ) this.ready = true;
  if( ! this.ready ) {
    this.ready = false;
    this.obj.Eval(this);
  }
  return this.ready;
}

function stateContinue() {
  this.cc.cont(this);
}

State.prototype.Eval = stateEval;
State.prototype.cont = stateContinue;

function Ex(s) { this.s = s; }
Ex.prototype.Str = function(){ return "#error<"+this.s+">"; }
Ex.prototype.Content = function(){ return this.s; }
Ex.prototype.Html = dumbHtml;

getSymbol('(').Eval = getSymbol(')').Eval = function() {
  throw new Ex('unbalanced bracket '+this.name);
}

var topCC = new Continuation(null,null,null,function(state){throw state;});

function doEval( obj, noTrans ) {
  try {
    if( obj instanceof Symbol && obj.Eval == Symbol.prototype.Eval )
      return TopEnv.get(obj.name);

    if( ! noTrans ) {
      try {
        var xformer = TopEnv.get('transform');
        if( xformer instanceof Lambda || xformer instanceof Function ) {
          var o = doEval( new Pair( xformer,
                        new Pair( new Pair( theQuote,
                                  new Pair( obj,
                                  theNil )),
                        theNil)), true );
          if( ! (o instanceof Ex) ) obj = o;
        }
      } catch( ex ) { }
    }

    var state = new State( obj, TopEnv, topCC );
    while( true ) {

      // Both state.Eval() and state.cont()
      // returns True if value was calculated
      // or False if continuation

      if( state.Eval(noTrans) ) {
        state.ready = false;
        state.cont();
      }
    }
  } catch(e) {
    if( e instanceof Ex )
      throw e;
    else if( e instanceof State )
      return e.obj;
    else 
      throw new Ex(e.description); // throw e;
  }
}

function evalTrue(state) {
  state.ready = true;
}

function evalVar(state) {
  state.obj = state.env.get(this.name);
  state.ready = true;
}

// ?? Continuation

function Continuation(obj,env,cc,f) {
  this.i = 0; // for List-cont
  this.obj = obj;
  this.env = env;
  this.cc = cc;
  this.cont = f;
}

Continuation.prototype.clone = function() {
  var r = clone( this );
  if( this.cc ) r.cc = this.cc.clone();
  return r;
}

function continuePair(state) {
  this[this.i++] = state.obj;
  if( isNil(this.obj) ) {
    // apply: 1. create arg list
    var args = theNil, prev = args;
    for( var i = 1; i < this.i; i++ ) {
      var cur = new Pair( this[i], theNil );
      if( args == theNil ) args = cur; else prev.cdr = cur;
      prev = cur;
    }
    // 2. call f()
    state.env = this.env;
    state.cc = this.cc;
    state.obj = callF( this[0], args, state );
  } else {
    state.obj = this.obj.car;
    state.env = this.env;
    state.cc = this;
    this.obj = this.obj.cdr;   // 2Do: (a.b) list!!
    state.ready = false;
  }
}

Pair.prototype.ListCopy = function() {
  var o,p,r = new Pair(this.car);
  for( o = this.cdr, p=r; o instanceof Pair; p=p.cdr=new Pair(o.car), o=o.cdr );
  p.cdr = o; return r;
}

function callF( f, args, state ) {

 Again: while(true) {

  if( typeof( f ) == 'function' ) {
    state.ready = true;
    return f(args,state);

  } else if( f instanceof Lambda ) {

    // map arguments to new env variables
    state.env = new Env(f.env);

    for( var vars = f.args, vals = args;
         (vars instanceof Pair) && !isNil(vars);
         vars = vars.cdr, vals = vals.cdr ) {
      if( vars.car instanceof Symbol ) {
        state.env[ vars.car.name ] = vals.car;
      } else throw new Ex("lambda arg is not symbol");
    }
    if( vars instanceof Symbol ) {
      state.env[ vars.name ] = vals;
    } else if( ! isNil(vars) ) throw new Ex("lambda args are not symbols");

    state.ready = false;
    return f.body;

  } else if( f instanceof Continuation ) {
    state.ready = true;
    state.cc = f.clone();
    // continue - multiple values case...
    if( state.cc.cont == continuePair ) {
      while( !isNil(args.cdr) ) {
        state.cc[state.cc.i++] = args.car;
        args = args.cdr;
      }
    }
    // if( state.cc == topCC ) { }
    return args.car;

  } else {
    throw new Ex("call to non-function " + ( f && f.Str ? f.Str() : f)
                 + (trace ? " with "+args.Str() : ''));
  }
}}

function continueDefine(state) {
  state.env = this.env;
  state.cc = this.cc;
  if( this.define ) {
    state.env[this.obj.name] = state.obj;
  } else {
    state.env.set( this.obj.name, state.obj );
  }
  state.ready = true;
}

function continueBegin(state) {
  state.obj = this.obj.car;
  state.env = this.env;
  state.ready = false;
  if( isNil(this.obj.cdr) ) {
    state.cc = this.cc;
  } else {
    this.obj = this.obj.cdr;
    state.cc = this;
  }
}

function continueIf(state) {
  state.obj = state.obj ? this.obj.car : this.obj.cdr.car;
  state.env = this.env;
  state.cc = this.cc;
  state.ready = false;
}

function continueSyntax(state) {
  state.env = this.env;
  state.cc = this.cc;
  state.ready = false;
}

function evalPair(state) {

  if( isNil(this) ) throw new Ex('Scheme is not Lisp, cannot eval ()');

  var f = (this.car instanceof Symbol) ? state.env.get(this.car.name) : null;

  // lambda, (define (f ...) ...)

  if( f == theLambda || (f == theDefine && (this.cdr.car instanceof Pair)) ) {

    // get function arguments and body

    var args, body;
    if( f == theLambda ) {
      args = this.cdr.car;
      body = this.cdr.cdr;
    } else {  // define
      args = this.cdr.car.cdr;
      body = this.cdr.cdr;
    }

    // create function object

    state.obj = new Lambda( args,
                            isNil(body.cdr) ? body.car :
                            new Pair( getSymbol("begin"), body ),
                            state.env );

    // define

    if( f == theDefine ) {
      state.env[ this.cdr.car.car.name ] = state.obj;
    }

    // OK, don't need to evaluate it any more

    state.ready = true;

  // define, set!

  } else if( f == theDefine || f == theSet ) {

    state.obj = this.cdr.cdr.car;
    state.cc = new Continuation( this.cdr.car, state.env, state.cc, continueDefine );
    state.cc.define = f == theDefine;
    state.ready = false; // evaluate expression first

  // begin

  } else if( f == theBegin ) {

    state.obj = this.cdr.car;
   // if( state.env != TopEnv )
   //   state.env = new Env(state.env);  // 2Do: that is wrong!!
    if( ! isNil(this.cdr.cdr) ) {
      state.cc = new Continuation( this.cdr.cdr, state.env, state.cc, continueBegin );
    }
    state.ready = false;

  // quote

  } else if( f == theQuote ) {
    state.obj = this.cdr.car;
    state.ready = true;

  // if

  } else if( f == theIf ) {
    state.obj = this.cdr.car;
    state.cc = new Continuation( this.cdr.cdr, state.env, state.cc, continueIf );
    state.ready = false;

  // define-syntax

  } else if( f == theDefineSyntax ) {

    state.env[ (state.obj = this.cdr.car).name ] = new Syntax(
      state.env.get(this.cdr.cdr.car.car.name), this.cdr.cdr.car.cdr );
    state.ready = true;

  // Syntax...

  } else if( f instanceof Syntax ) {

    state.cc = new Continuation( null, state.env, state.cc, continueSyntax );
    state.obj = callF( f.transformer, new Pair(state.obj, f.args), state );

  // (...)

  } else {
    state.obj = this.car;
    state.cc = new Continuation( this.cdr, state.env, state.cc, continuePair );
    state.ready = false;
  }
}

Nil.prototype.Eval = evalTrue;
Boolean.prototype.Eval = evalTrue;
Char.prototype.Eval = evalTrue;
Number.prototype.Eval = evalTrue;
Pair.prototype.Eval = evalPair;
String.prototype.Eval = evalTrue;
Symbol.prototype.Eval = evalVar;
Lambda.prototype.Eval = evalTrue;
Array.prototype.Eval = evalTrue;
Continuation.prototype.Eval = evalTrue;
Ex.prototype.Eval = evalTrue;
Function.prototype.Eval = evalTrue; // 2Do: throw Ex??

//
// Syntax transformers...
//

function Syntax( transformer, args ) {
  this.transformer = transformer;
  this.args = args;
}

Syntax.prototype.Eval = evalTrue;
Syntax.prototype.Html = dumbHtml;
Syntax.prototype.Str = function() { return '#syntax'; }

// syntax keywords

TopEnv['begin'] = theBegin = getSymbol('begin');
TopEnv['quote'] = theQuote = getSymbol('quote');
TopEnv['if'] = theIf = getSymbol('if');
TopEnv['define'] = theDefine = getSymbol('define');
TopEnv['set!'] = theSet = getSymbol('set!');
TopEnv['lambda'] = theLambda = getSymbol('lambda');
TopEnv['define-syntax'] = theDefineSyntax = getSymbol('define-syntax');
TopEnv['unquote'] = getSymbol('unquote');
TopEnv['unquote-splicing'] = getSymbol('unquote-splicing');

//
// Built-in functions
//

TopEnv['+'] = function(list) {
  var result = 0;
  while( list instanceof Pair ) {
    if( typeof(list.car)=='number' ) result += list.car;
    list = list.cdr;
  }
  return result;
}

TopEnv['*'] = function(list) {
  var result = 1;
  while( ! isNil(list) ) {
    result *= list.car.valueOf();
    list = list.cdr;
  }
  return result;
}

TopEnv['-'] = function(list) {
  var result = 0, count = 0;
  while( ! isNil(list) ) {
    var o = list.car.valueOf();
    result += (count++ > 0 ? -o : o);
    list = list.cdr;
  }
  return count > 1 ? result : -result;
}

TopEnv['/'] = function(list) {
  var result = 1, count = 0;
  while( ! isNil(list) ) {
    var o = list.car.valueOf();
    result *= (count++ > 0 ? 1/o : o);
    list = list.cdr;
  }
  return count > 1 ? result : 1/result;
}

TopEnv['string-append'] = function(list) {
  var result = '';
  while( ! isNil(list) ) {
    result += list.car;
    list = list.cdr;
  }
  return result;
}

TopEnv['string'] = function(list) {
  var result = '';
  while( ! isNil(list) ) {
    result += list.car.value;
    list = list.cdr;
  }
  return result;
}

TopEnv['vector'] = function(list) {
  var result = new Array();
  while( ! isNil(list) ) {
    result[result.length] = list.car;
    list = list.cdr;
  }
  return result;
}

TopEnv['string->list'] = function(list) {
  var i, result = theNil;
  for( i = list.car.length-1; i >= 0; --i ) {
    result = new Pair( getChar(list.car.charAt(i)), result );
  }
  return result;
}

// fixed arguments

TopEnv['car'] = function(list) { return list.car.car; }
TopEnv['cdr'] = function(list) { return list.car.cdr; }
TopEnv['cons'] = function(list) { return new Pair(list.car,list.cdr.car); }

TopEnv['eval'] = function(list) { return doEval(list.car); }
TopEnv['string->symbol'] = function(list) { return getSymbol(list.car,true); }
TopEnv['symbol->string'] = function(list) { return list.car.name; }

TopEnv['encode'] = function(list) { return encodeURIComponent(list.car); }

function truncate(x) {
  return x > 0 ? Math.floor(x) : Math.ceil(x);
}

TopEnv['ceiling'] = function(list) { return Math.ceil(list.car); }
TopEnv['floor'] = function(list) { return Math.floor(list.car); }
TopEnv['truncate'] = function(list) { return truncate(list.car); }
TopEnv['sqrt'] = function(list) { return Math.sqrt(list.car); }
TopEnv['exp'] = function(list) { return Math.exp(list.car); }
TopEnv['expt'] = function(list) { return Math.pow(list.car,list.cdr.car); }
TopEnv['log'] = function(list) { return Math.log(list.car); }
TopEnv['sin'] = function(list) { return Math.sin(list.car); }
TopEnv['cos'] = function(list) { return Math.cos(list.car); }
TopEnv['asin'] = function(list) { return Math.asin(list.car); }
TopEnv['acos'] = function(list) { return Math.acos(list.car); }
TopEnv['tan'] = function(list) { return Math.tan(list.car); }

TopEnv['atan'] = function(list) {
  return isNil(list.cdr) ? Math.atan(list.car)
                         : Math.atan2(list.car,list.cdr.car);
}

TopEnv['integer?'] = function(list) { return list.car == Math.round(list.car); }
TopEnv['quotient'] = function(list) { return truncate(list.car / list.cdr.car); }
TopEnv['remainder'] = function(list) { return list.car % list.cdr.car; }
TopEnv['modulo'] = function(list) {
  var v = list.car % list.cdr.car;
  if( v && (list.car < 0) != (list.cdr.car < 0) ) v += list.cdr.car;
  return v;
}
TopEnv['round'] = function(list) { return Math.round(list.car); }

TopEnv['apply'] = function(list,state) {
  var f = list.car, cur;
  for( cur = list; !isNil(cur.cdr.cdr); cur = cur.cdr );
  cur.cdr = cur.cdr.car;
  return callF( list.car, list.cdr, state );
}

TopEnv['clone'] = function(list,state) {
  return list.car.clone(state.env);
}

function isEq(a,b) { return a==b || isNil(a)&&isNil(b); }

TopEnv['string=?'] =
TopEnv['char=?'] =
TopEnv['eqv?'] =
TopEnv['='] =
TopEnv['eq?'] = function(list) { return isEq(list.car,list.cdr.car); }

TopEnv['substring'] = function(list) {
  return list.car.substring( list.cdr.car, list.cdr.cdr.car );
}

TopEnv['string>?'] =
TopEnv['>'] = function(list) { return list.car > list.cdr.car; }
TopEnv['string<?'] =
TopEnv['<'] = function(list) { return list.car < list.cdr.car; }
TopEnv['string>=?'] =
TopEnv['>='] = function(list) { return list.car >= list.cdr.car; }
TopEnv['string<=?'] =
TopEnv['<='] = function(list) { return list.car <= list.cdr.car; }

TopEnv['char>?'] = function(list) { return list.car.value > list.cdr.car.value; }
TopEnv['char<?'] = function(list) { return list.car.value < list.cdr.car.value; }
TopEnv['char>=?'] = function(list) { return list.car.value >= list.cdr.car.value; }
TopEnv['char<=?'] = function(list) { return list.car.value <= list.cdr.car.value; }

TopEnv['char-downcase'] = function(list) { return getChar(list.car.value.toLowerCase()); }
TopEnv['char-upcase'] = function(list) { return getChar(list.car.value.toUpperCase()); }
TopEnv['string-downcase'] = function(list) { return list.car.toLowerCase(); }
TopEnv['string-upcase'] = function(list) { return list.car.toUpperCase(); }

TopEnv['char->integer'] = function(list) { return list.car.value.charCodeAt(0); }
TopEnv['integer->char'] = function(list) {
  return getChar( String.fromCharCode(list.car) );
}

TopEnv['make-string'] = function(list) {
  var s = '', i;
  for( i = 0; i < list.car; i++ ) {
    s += list.cdr.car.value;
  }
  return s;
}
TopEnv['rnd'] = function(list) { return Math.random(); }
TopEnv['string->number'] = function(list) {
  return list.cdr.car ? parseInt(list.car,list.cdr.car) : parseFloat(list.car);
}
TopEnv['number->string'] = function(list) {
  return list.cdr.car ? list.car.toString(list.cdr.car) : ''+list.car;
}

TopEnv['set-car!'] = function(list) { list.car.car = list.cdr.car; return list.car; }
TopEnv['set-cdr!'] = function(list) { list.car.cdr = list.cdr.car; return list.car; }

TopEnv['vector-length'] =
TopEnv['string-length'] = function(list) { return list.car.length; }

TopEnv['string-ref'] = function(list) {
  return getChar(list.car.charAt(list.cdr.car));
}
TopEnv['get-prop'] =
TopEnv['vector-ref'] = function(list) { return list.car[list.cdr.car]; }
TopEnv['set-prop!'] =
TopEnv['vector-set!'] = function(list) { list.car[list.cdr.car] = list.cdr.cdr.car; }
TopEnv['make-vector'] = function(list) { var v = new Array(), i;
for( i=0; i<list.car; i++ ) v[i]=list.cdr.car; return v;
}

TopEnv['str'] = function(list) { return Str(list.car); }
TopEnv['html'] = function(list) { return Html(list.car); }

/* (alert "a message") */
TopEnv['alert'] = function(list) {
  alert(list.car);
}

/* (ajax-get url function) */
TopEnv['ajax-get'] = function(list) {
  $.get(list.car, function (xml) {
    doEval (new Pair(list.cdr.car, new Pair(new Pair(theQuote, new
    Pair(xml,theNil)), theNil)), true)
  })
}

/* (set-timeout! handler timeout) */
TopEnv['set-timeout!'] = function(list) {
  setTimeout(function () {
    doEval (new Pair(list.car, theNil), true);
  }, list.cdr.car)
}

/* (set-handler! object name handler) */
TopEnv['set-handler!'] = function(list) {
  list.car[list.cdr.car] = function() {
    doEval( new Pair( list.cdr.cdr.car,
            new Pair( new Pair( theQuote,
                      new Pair( this, theNil )), theNil)), true);
  }
}
TopEnv['list-props'] = function(list) {
  var r = theNil, i;
  for( i in list.car ) r = new Pair(i,r);
  return r;
}
TopEnv['parse'] = function(list) {
  var r = theNil, c = r, p = new Parser(list.car), o;
  while( (o = p.getObject()) != null ) {
    o = new Pair(o, theNil );
    if( r == theNil ) r = o; else c.cdr = o;
    c = o;
  }
  return r;
}
TopEnv['type-of'] = function(list) { return objType(list.car); }
TopEnv['js-call'] = function(list) {
  if( isNil( list.cdr ) ) {
    return list.car();
  } else if( isNil( list.cdr.cdr ) ) {
    return list.car( list.cdr.car );
  } else if( isNil( list.cdr.cdr.cdr ) ) {
    return list.car( list.cdr.car, list.cdr.cdr.car );
  } else {
    return list.car( list.cdr.car, list.cdr.cdr.car, list.cdr.cdr.cdr.car );
  }
}
TopEnv['js-invoke'] = function(list) {
  if( isNil( list.cdr.cdr ) ) {
    return list.car[list.cdr.car]();
  } else if( isNil( list.cdr.cdr.cdr ) ) {
    return list.car[list.cdr.car]( list.cdr.cdr.car );
  } else if( isNil( list.cdr.cdr.cdr.cdr ) ) {
    return list.car[list.cdr.car]( list.cdr.cdr.car, list.cdr.cdr.cdr.car );
  } else {
    return list.car[list.cdr.car]( list.cdr.cdr.car, list.cdr.cdr.cdr.car, list.cdr.cdr.cdr.cdr.car );
  }
}

function isPair(x) { return (x instanceof Pair) && !isNil(x); }
TopEnv['pair?'] = function(list) { return isPair(list.car); }

TopEnv['boolean?'] = function(list) { return typeof(list.car)=='boolean'; }
TopEnv['string?'] = function(list) { return typeof(list.car)=='string'; }
TopEnv['number?'] = function(list) { return typeof(list.car)=='number'; }
TopEnv['null?'] = function(list) { return isNil(list.car); }
TopEnv['symbol?'] = function(list) { return list.car instanceof Symbol; }
TopEnv['syntax?'] = function(list) { return list.car instanceof Syntax; }
TopEnv['char?'] = function(list) { return list.car instanceof Char; }
TopEnv['vector?'] = function(list) { return list.car instanceof Array; }
TopEnv['procedure?'] = function(list) {
  return list.car instanceof Function ||
         list.car instanceof Lambda ||
         list.car instanceof Continuation;
}
TopEnv['lambda?'] = function(list) { return list.car instanceof Lambda; }
TopEnv['function?'] = function(list) { return list.car instanceof Function; }
TopEnv['continuation?'] = function(list) { return list.car instanceof Continuation; }

TopEnv['js-eval'] = function(list) { return eval(list.car); }

// changed by MH
// error can take multiple arguments
TopEnv['error'] = function(list) { 
    var out_string = list.car;
    list = list.cdr;
    while (list.car != undefined) {
	out_string = out_string + " "+list.car.Str();
	list = list.cdr;
    }
    throw new Ex(out_string); 
}

TopEnv['trace'] = function(list) { trace = list.car.valueOf(); }
// changed by MH 19/6/2008
// TopEnv['read'] = function(list) { return TopParser.getObject(); }
TopEnv['read'] = function(list) { 
    var default_string = (window.scheme_statement != undefined) ? scheme_statement : '';
    var prompt_result = prompt('Enter Scheme expression',default_string);
    if (prompt_result != null) {
	return new Parser(prompt_result).getObject();
    }
    else return theNil;
}
TopEnv['write'] = function(list) { return; }
TopEnv['newline'] = function(list) { return; }
TopEnv['write-char'] =
TopEnv['display'] = function(list) {
    return;
}
TopEnv['nil'] = theNil;

TopEnv['eof-object?'] =
TopEnv['js-null?'] = function(list) { return list.car == null; }

theCallCC =
TopEnv['call-with-current-continuation'] = function(list,state) {
  state.ready = false;
  return callF( list.car, new Pair( state.cc.clone(), theNil ), state );
}

var genSymBase = 0;
TopEnv['gen-sym'] = function() { return getSymbol('_'+(genSymBase++)+'_'); }

// added by MH on 14/6/2008

// do not use toplevel name "display"; it is pre-defined in JavaScript
window.__display = function(list) {
    var toShow = ( typeof list.car == "string" ) ? list.car : list.car.Str();
    window[theText] = window[theText] + toShow;
    document['form_'+theText].resultScheme.value = window[theText];
    document['form_'+theText].resultScheme.scrollTop 
	    = document['form_'+theText].resultScheme.scrollHeight;
    return getSymbol('ok');
}

TopEnv['display'] = window.__display;

TopEnv['newline'] = function(list) { 
    return window.__display({car:"\n"});
}

TopEnv['runtime'] = function(list) { 
    var d = new Date();
    return d.getTime();
}

//
// Read-Eval-Print-Loop
//

function schemeEval(txt) {
    var o, res = null;
    TopParser = new Parser( txt );
    while( ( o = TopParser.getObject() ) != null ) {
	o = doEval( o );
	if( o != null ) res = o;
    }
    return res.Str();
}

// Need to wrap alert as calling it from Scheme
// in Firefox otherwise doesn't work
function jsAlert(text) {
  alert(text)
}

// Need to wrap settimeout as calling it from Scheme
// in Firefox otherwise doesn't work
function jsSetTimeout(f,t) {
  setTimeout(f,t)
}

function schemeInit() {

// Library begin

/*
  var o, p = new Parser( document.getElementById('lib').innerHTML );
  while( (o = p.getObject()) != null ) {
    doEval(o);
  }
*/

var e=TopEnv;
e['call/cc']=e.get('call-with-current-continuation');
e['list']=new Lambda(getSymbol('x'),getSymbol('x'),e,function(list){var r,e=new Env(this.env);while(true){e['x']=list;r=e['x'];if(r!=theTC||r.f!=this)return r}});
e['not']=new Lambda(new Pair(getSymbol('x'),theNil),new Pair(getSymbol('if'),new Pair(getSymbol('x'),new Pair(false,new Pair(true,theNil)))),e,function(list){var r,e=new Env(this.env);while(true){e['x']=list.car;r=((e['x'])!=false?false:true);if(r!=theTC||r.f!=this)return r}});
e['negative?']=new Lambda(new Pair(getSymbol('x'),theNil),new Pair(getSymbol('<'),new Pair(getSymbol('x'),new Pair(0,theNil))),e,function(list){var r,e=new Env(this.env);while(true){e['x']=list.car;r=e['x']<0;if(r!=theTC||r.f!=this)return r}});
e['positive?']=new Lambda(new Pair(getSymbol('x'),theNil),new Pair(getSymbol('>'),new Pair(getSymbol('x'),new Pair(0,theNil))),e,function(list){var r,e=new Env(this.env);while(true){e['x']=list.car;r=e['x']>0;if(r!=theTC||r.f!=this)return r}});
e['even?']=new Lambda(new Pair(getSymbol('x'),theNil),new Pair(getSymbol('='),new Pair(new Pair(getSymbol('remainder'),new Pair(getSymbol('x'),new Pair(2,theNil))),new Pair(0,theNil))),e,function(list){var r,e=new Env(this.env);while(true){e['x']=list.car;r=isEq(Apply(TopEnv.get('remainder'),new Pair(e['x'],new Pair(2,theNil))),0);if(r!=theTC||r.f!=this)return r}});
e['odd?']=new Lambda(new Pair(getSymbol('x'),theNil),new Pair(getSymbol('not'),new Pair(new Pair(getSymbol('even?'),new Pair(getSymbol('x'),theNil)),theNil)),e,function(list){var r,e=new Env(this.env);while(true){e['x']=list.car;r=(Apply(TopEnv.get('even?'),new Pair(e['x'],theNil))==false);if(r!=theTC||r.f!=this)return r}});
e['zero?']=new Lambda(new Pair(getSymbol('x'),theNil),new Pair(getSymbol('='),new Pair(getSymbol('x'),new Pair(0,theNil))),e,function(list){var r,e=new Env(this.env);while(true){e['x']=list.car;r=isEq(e['x'],0);if(r!=theTC||r.f!=this)return r}});
e['abs']=new Lambda(new Pair(getSymbol('x'),theNil),new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('<'),new Pair(getSymbol('x'),new Pair(0,theNil))),new Pair(new Pair(getSymbol('-'),new Pair(getSymbol('x'),theNil)),new Pair(getSymbol('x'),theNil)))),e,function(list){var r,e=new Env(this.env);while(true){e['x']=list.car;r=((e['x']<0)!=false?(-e['x']):e['x']);if(r!=theTC||r.f!=this)return r}});
e['magnitude']=e.get('abs');
e['exact?']=e.get('integer?');
e['inexact?']=new Lambda(new Pair(getSymbol('x'),theNil),new Pair(getSymbol('not'),new Pair(new Pair(getSymbol('exact?'),new Pair(getSymbol('x'),theNil)),theNil)),e,function(list){var r,e=new Env(this.env);while(true){e['x']=list.car;r=(Apply(TopEnv.get('exact?'),new Pair(e['x'],theNil))==false);if(r!=theTC||r.f!=this)return r}});
e['random']=new Lambda(new Pair(getSymbol('x'),theNil),new Pair(getSymbol('floor'),new Pair(new Pair(getSymbol('*'),new Pair(new Pair(getSymbol('rnd'),theNil),new Pair(getSymbol('x'),theNil))),theNil)),e,function(list){var r,e=new Env(this.env);while(true){e['x']=list.car;r=TC(TopEnv.get('floor'),list=new Pair((Apply(TopEnv.get('rnd'),theNil)*e['x']),theNil));if(r!=theTC||r.f!=this)return r}});
e['char-ci=?']=new Lambda(new Pair(getSymbol('x'),new Pair(getSymbol('y'),theNil)),new Pair(getSymbol('char=?'),new Pair(new Pair(getSymbol('char-downcase'),new Pair(getSymbol('x'),theNil)),new Pair(new Pair(getSymbol('char-downcase'),new Pair(getSymbol('y'),theNil)),theNil))),e,function(list){var r,e=new Env(this.env);while(true){e['x']=list.car;e['y']=list.cdr.car;r=isEq(Apply(TopEnv.get('char-downcase'),new Pair(e['x'],theNil)),Apply(TopEnv.get('char-downcase'),new Pair(e['y'],theNil)));if(r!=theTC||r.f!=this)return r}});
e['char-ci>?']=new Lambda(new Pair(getSymbol('x'),new Pair(getSymbol('y'),theNil)),new Pair(getSymbol('char>?'),new Pair(new Pair(getSymbol('char-downcase'),new Pair(getSymbol('x'),theNil)),new Pair(new Pair(getSymbol('char-downcase'),new Pair(getSymbol('y'),theNil)),theNil))),e,function(list){var r,e=new Env(this.env);while(true){e['x']=list.car;e['y']=list.cdr.car;r=TC(TopEnv.get('char>?'),list=new Pair(Apply(TopEnv.get('char-downcase'),new Pair(e['x'],theNil)),new Pair(Apply(TopEnv.get('char-downcase'),new Pair(e['y'],theNil)),theNil)));if(r!=theTC||r.f!=this)return r}});
e['char-ci<?']=new Lambda(new Pair(getSymbol('x'),new Pair(getSymbol('y'),theNil)),new Pair(getSymbol('char<?'),new Pair(new Pair(getSymbol('char-downcase'),new Pair(getSymbol('x'),theNil)),new Pair(new Pair(getSymbol('char-downcase'),new Pair(getSymbol('y'),theNil)),theNil))),e,function(list){var r,e=new Env(this.env);while(true){e['x']=list.car;e['y']=list.cdr.car;r=TC(TopEnv.get('char<?'),list=new Pair(Apply(TopEnv.get('char-downcase'),new Pair(e['x'],theNil)),new Pair(Apply(TopEnv.get('char-downcase'),new Pair(e['y'],theNil)),theNil)));if(r!=theTC||r.f!=this)return r}});
e['char-ci>=?']=new Lambda(new Pair(getSymbol('x'),new Pair(getSymbol('y'),theNil)),new Pair(getSymbol('char>=?'),new Pair(new Pair(getSymbol('char-downcase'),new Pair(getSymbol('x'),theNil)),new Pair(new Pair(getSymbol('char-downcase'),new Pair(getSymbol('y'),theNil)),theNil))),e,function(list){var r,e=new Env(this.env);while(true){e['x']=list.car;e['y']=list.cdr.car;r=TC(TopEnv.get('char>=?'),list=new Pair(Apply(TopEnv.get('char-downcase'),new Pair(e['x'],theNil)),new Pair(Apply(TopEnv.get('char-downcase'),new Pair(e['y'],theNil)),theNil)));if(r!=theTC||r.f!=this)return r}});
e['char-ci<=?']=new Lambda(new Pair(getSymbol('x'),new Pair(getSymbol('y'),theNil)),new Pair(getSymbol('char<=?'),new Pair(new Pair(getSymbol('char-downcase'),new Pair(getSymbol('x'),theNil)),new Pair(new Pair(getSymbol('char-downcase'),new Pair(getSymbol('y'),theNil)),theNil))),e,function(list){var r,e=new Env(this.env);while(true){e['x']=list.car;e['y']=list.cdr.car;r=TC(TopEnv.get('char<=?'),list=new Pair(Apply(TopEnv.get('char-downcase'),new Pair(e['x'],theNil)),new Pair(Apply(TopEnv.get('char-downcase'),new Pair(e['y'],theNil)),theNil)));if(r!=theTC||r.f!=this)return r}});
e['char-lower-case?']=new Lambda(new Pair(getSymbol('x'),theNil),new Pair(getSymbol('char=?'),new Pair(getSymbol('x'),new Pair(new Pair(getSymbol('char-downcase'),new Pair(getSymbol('x'),theNil)),theNil))),e,function(list){var r,e=new Env(this.env);while(true){e['x']=list.car;r=isEq(e['x'],Apply(TopEnv.get('char-downcase'),new Pair(e['x'],theNil)));if(r!=theTC||r.f!=this)return r}});
e['char-upper-case?']=new Lambda(new Pair(getSymbol('x'),theNil),new Pair(getSymbol('char=?'),new Pair(getSymbol('x'),new Pair(new Pair(getSymbol('char-upcase'),new Pair(getSymbol('x'),theNil)),theNil))),e,function(list){var r,e=new Env(this.env);while(true){e['x']=list.car;r=isEq(e['x'],Apply(TopEnv.get('char-upcase'),new Pair(e['x'],theNil)));if(r!=theTC||r.f!=this)return r}});
e['char-alphabetic?']=new Lambda(new Pair(getSymbol('x'),theNil),new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('char-ci>=?'),new Pair(getSymbol('x'),new Pair(getChar('a'),theNil))),new Pair(new Pair(getSymbol('char-ci<=?'),new Pair(getSymbol('x'),new Pair(getChar('z'),theNil))),new Pair(false,theNil)))),e,function(list){var r,e=new Env(this.env);while(true){e['x']=list.car;r=((Apply(TopEnv.get('char-ci>=?'),new Pair(e['x'],new Pair(getChar('a'),theNil))))!=false?TC(TopEnv.get('char-ci<=?'),list=new Pair(e['x'],new Pair(getChar('z'),theNil))):false);if(r!=theTC||r.f!=this)return r}});
e['char-numeric?']=new Lambda(new Pair(getSymbol('x'),theNil),new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('char>=?'),new Pair(getSymbol('x'),new Pair(getChar('0'),theNil))),new Pair(new Pair(getSymbol('char<=?'),new Pair(getSymbol('x'),new Pair(getChar('9'),theNil))),new Pair(false,theNil)))),e,function(list){var r,e=new Env(this.env);while(true){e['x']=list.car;r=((Apply(TopEnv.get('char>=?'),new Pair(e['x'],new Pair(getChar('0'),theNil))))!=false?TC(TopEnv.get('char<=?'),list=new Pair(e['x'],new Pair(getChar('9'),theNil))):false);if(r!=theTC||r.f!=this)return r}});
e['char-whitespace?']=new Lambda(new Pair(getSymbol('x'),theNil),new Pair(getSymbol('char<=?'),new Pair(getSymbol('x'),new Pair(getChar(' '),theNil))),e,function(list){var r,e=new Env(this.env);while(true){e['x']=list.car;r=TC(TopEnv.get('char<=?'),list=new Pair(e['x'],new Pair(getChar(' '),theNil)));if(r!=theTC||r.f!=this)return r}});
e['string-ci=?']=new Lambda(new Pair(getSymbol('x'),new Pair(getSymbol('y'),theNil)),new Pair(getSymbol('string=?'),new Pair(new Pair(getSymbol('string-downcase'),new Pair(getSymbol('x'),theNil)),new Pair(new Pair(getSymbol('string-downcase'),new Pair(getSymbol('y'),theNil)),theNil))),e,function(list){var r,e=new Env(this.env);while(true){e['x']=list.car;e['y']=list.cdr.car;r=isEq(Apply(TopEnv.get('string-downcase'),new Pair(e['x'],theNil)),Apply(TopEnv.get('string-downcase'),new Pair(e['y'],theNil)));if(r!=theTC||r.f!=this)return r}});
e['string-ci>?']=new Lambda(new Pair(getSymbol('x'),new Pair(getSymbol('y'),theNil)),new Pair(getSymbol('string>?'),new Pair(new Pair(getSymbol('string-downcase'),new Pair(getSymbol('x'),theNil)),new Pair(new Pair(getSymbol('string-downcase'),new Pair(getSymbol('y'),theNil)),theNil))),e,function(list){var r,e=new Env(this.env);while(true){e['x']=list.car;e['y']=list.cdr.car;r=TC(TopEnv.get('string>?'),list=new Pair(Apply(TopEnv.get('string-downcase'),new Pair(e['x'],theNil)),new Pair(Apply(TopEnv.get('string-downcase'),new Pair(e['y'],theNil)),theNil)));if(r!=theTC||r.f!=this)return r}});
e['string-ci<?']=new Lambda(new Pair(getSymbol('x'),new Pair(getSymbol('y'),theNil)),new Pair(getSymbol('string<?'),new Pair(new Pair(getSymbol('string-downcase'),new Pair(getSymbol('x'),theNil)),new Pair(new Pair(getSymbol('string-downcase'),new Pair(getSymbol('y'),theNil)),theNil))),e,function(list){var r,e=new Env(this.env);while(true){e['x']=list.car;e['y']=list.cdr.car;r=TC(TopEnv.get('string<?'),list=new Pair(Apply(TopEnv.get('string-downcase'),new Pair(e['x'],theNil)),new Pair(Apply(TopEnv.get('string-downcase'),new Pair(e['y'],theNil)),theNil)));if(r!=theTC||r.f!=this)return r}});
e['string-ci>=?']=new Lambda(new Pair(getSymbol('x'),new Pair(getSymbol('y'),theNil)),new Pair(getSymbol('string>=?'),new Pair(new Pair(getSymbol('string-downcase'),new Pair(getSymbol('x'),theNil)),new Pair(new Pair(getSymbol('string-downcase'),new Pair(getSymbol('y'),theNil)),theNil))),e,function(list){var r,e=new Env(this.env);while(true){e['x']=list.car;e['y']=list.cdr.car;r=TC(TopEnv.get('string>=?'),list=new Pair(Apply(TopEnv.get('string-downcase'),new Pair(e['x'],theNil)),new Pair(Apply(TopEnv.get('string-downcase'),new Pair(e['y'],theNil)),theNil)));if(r!=theTC||r.f!=this)return r}});
e['string-ci<=?']=new Lambda(new Pair(getSymbol('x'),new Pair(getSymbol('y'),theNil)),new Pair(getSymbol('string<=?'),new Pair(new Pair(getSymbol('string-downcase'),new Pair(getSymbol('x'),theNil)),new Pair(new Pair(getSymbol('string-downcase'),new Pair(getSymbol('y'),theNil)),theNil))),e,function(list){var r,e=new Env(this.env);while(true){e['x']=list.car;e['y']=list.cdr.car;r=TC(TopEnv.get('string<=?'),list=new Pair(Apply(TopEnv.get('string-downcase'),new Pair(e['x'],theNil)),new Pair(Apply(TopEnv.get('string-downcase'),new Pair(e['y'],theNil)),theNil)));if(r!=theTC||r.f!=this)return r}});
e['map']=new Lambda(new Pair(getSymbol('f'),new Pair(getSymbol('ls'),getSymbol('more'))),new Pair(getSymbol('begin'),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('map1'),new Pair(new Pair(getSymbol('clone'),new Pair(getSymbol('_8_'),theNil)),theNil))),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('map-more'),new Pair(new Pair(getSymbol('clone'),new Pair(getSymbol('_9_'),theNil)),theNil))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('null?'),new Pair(getSymbol('more'),theNil)),new Pair(new Pair(getSymbol('map1'),new Pair(getSymbol('ls'),theNil)),new Pair(new Pair(getSymbol('map-more'),new Pair(getSymbol('ls'),new Pair(getSymbol('more'),theNil))),theNil)))),theNil)))),new Env(e).With('_8_',new Lambda(new Pair(getSymbol('l'),theNil),new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('null?'),new Pair(getSymbol('l'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(theNil,theNil)),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('pair?'),new Pair(getSymbol('l'),theNil)),new Pair(new Pair(getSymbol('cons'),new Pair(new Pair(getSymbol('f'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('l'),theNil)),theNil)),new Pair(new Pair(getSymbol('map1'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('l'),theNil)),theNil)),theNil))),new Pair(new Pair(getSymbol('f'),new Pair(getSymbol('l'),theNil)),theNil)))),theNil)))),e,function(list){var r,e=new Env(this.env);while(true){e['l']=list.car;r=(((e['l']==theNil))!=false?theNil:((((e['l'])instanceof Pair))!=false?new Pair(Apply(e.parentEnv['f'],new Pair(e['l'].car,theNil)),Apply(e.parentEnv['map1'],new Pair(e['l'].cdr,theNil))):TC(e.parentEnv['f'],list=new Pair(e['l'],theNil))));if(r!=theTC||r.f!=this)return r}})).With('_9_',new Lambda(new Pair(getSymbol('l'),new Pair(getSymbol('m'),theNil)),new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('null?'),new Pair(getSymbol('l'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(theNil,theNil)),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('pair?'),new Pair(getSymbol('l'),theNil)),new Pair(new Pair(getSymbol('cons'),new Pair(new Pair(getSymbol('apply'),new Pair(getSymbol('f'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('l'),theNil)),new Pair(new Pair(getSymbol('map'),new Pair(getSymbol('car'),new Pair(getSymbol('m'),theNil))),theNil)))),new Pair(new Pair(getSymbol('map-more'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('l'),theNil)),new Pair(new Pair(getSymbol('map'),new Pair(getSymbol('cdr'),new Pair(getSymbol('m'),theNil))),theNil))),theNil))),new Pair(new Pair(getSymbol('apply'),new Pair(getSymbol('f'),new Pair(getSymbol('l'),new Pair(getSymbol('m'),theNil)))),theNil)))),theNil)))),e,function(list){var r,e=new Env(this.env);while(true){e['l']=list.car;e['m']=list.cdr.car;r=(((e['l']==theNil))!=false?theNil:((((e['l'])instanceof Pair))!=false?new Pair(Apply(e.parentEnv['f'],new Pair(e['l'].car,Apply(TopEnv.get('map'),new Pair(TopEnv.get('car'),new Pair(e['m'],theNil))).ListCopy())),Apply(e.parentEnv['map-more'],new Pair(e['l'].cdr,new Pair(Apply(TopEnv.get('map'),new Pair(TopEnv.get('cdr'),new Pair(e['m'],theNil))),theNil)))):TC(e.parentEnv['f'],list=new Pair(e['l'],e['m'].ListCopy()))));if(r!=theTC||r.f!=this)return r}})),function(list){var r,e=new Env(this.env);while(true){e['f']=list.car;e['ls']=list.cdr.car;e['more']=list.cdr.cdr;r=(e['map1']=e.parentEnv['_8_'].clone(e),e['map-more']=e.parentEnv['_9_'].clone(e),(((e['more']==theNil))!=false?TC(e['map1'],list=new Pair(e['ls'],theNil)):TC(e['map-more'],list=new Pair(e['ls'],new Pair(e['more'],theNil)))));if(r!=theTC||r.f!=this)return r}});
e['map+']=new Lambda(new Pair(getSymbol('f'),getSymbol('lst')),new Pair(getSymbol('begin'),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('r'),new Pair(new Pair(getSymbol('quote'),new Pair(theNil,theNil)),theNil))),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('o'),new Pair(false,theNil))),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('p'),new Pair(false,theNil))),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('map-lst'),new Pair(new Pair(getSymbol('clone'),new Pair(getSymbol('_10_'),theNil)),theNil))),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('do-map'),new Pair(new Pair(getSymbol('clone'),new Pair(getSymbol('_11_'),theNil)),theNil))),new Pair(new Pair(getSymbol('do-map'),theNil),new Pair(getSymbol('r'),theNil)))))))),new Env(e).With('_10_',new Lambda(new Pair(getSymbol('op'),new Pair(getSymbol('l'),theNil)),new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('pair?'),new Pair(getSymbol('l'),theNil)),new Pair(new Pair(getSymbol('cons'),new Pair(new Pair(getSymbol('op'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('l'),theNil)),theNil)),new Pair(new Pair(getSymbol('map-lst'),new Pair(getSymbol('op'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('l'),theNil)),theNil))),theNil))),new Pair(new Pair(getSymbol('quote'),new Pair(theNil,theNil)),theNil)))),e,function(list){var r,e=new Env(this.env);while(true){e['op']=list.car;e['l']=list.cdr.car;r=((((e['l'])instanceof Pair))!=false?new Pair(Apply(e['op'],new Pair(e['l'].car,theNil)),Apply(e.parentEnv['map-lst'],new Pair(e['op'],new Pair(e['l'].cdr,theNil)))):theNil);if(r!=theTC||r.f!=this)return r}})).With('_11_',new Lambda(theNil,new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('pair?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('lst'),theNil)),theNil)),new Pair(new Pair(getSymbol('begin'),new Pair(new Pair(getSymbol('set!'),new Pair(getSymbol('o'),new Pair(new Pair(getSymbol('cons'),new Pair(new Pair(getSymbol('apply'),new Pair(getSymbol('f'),new Pair(new Pair(getSymbol('map'),new Pair(getSymbol('car'),new Pair(getSymbol('lst'),theNil))),theNil))),new Pair(new Pair(getSymbol('quote'),new Pair(theNil,theNil)),theNil))),theNil))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('null?'),new Pair(getSymbol('r'),theNil)),new Pair(new Pair(getSymbol('set!'),new Pair(getSymbol('r'),new Pair(getSymbol('o'),theNil))),new Pair(new Pair(getSymbol('set-cdr!'),new Pair(getSymbol('p'),new Pair(getSymbol('o'),theNil))),theNil)))),new Pair(new Pair(getSymbol('set!'),new Pair(getSymbol('p'),new Pair(getSymbol('o'),theNil))),new Pair(new Pair(getSymbol('set!'),new Pair(getSymbol('lst'),new Pair(new Pair(getSymbol('map'),new Pair(getSymbol('cdr'),new Pair(getSymbol('lst'),theNil))),theNil))),new Pair(new Pair(getSymbol('do-map'),theNil),theNil)))))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('not'),new Pair(new Pair(getSymbol('null?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('lst'),theNil)),theNil)),theNil)),new Pair(new Pair(getSymbol('if'),new Pair(getSymbol('p'),new Pair(new Pair(getSymbol('set-cdr!'),new Pair(getSymbol('p'),new Pair(new Pair(getSymbol('apply'),new Pair(getSymbol('f'),new Pair(getSymbol('lst'),theNil))),theNil))),new Pair(new Pair(getSymbol('set!'),new Pair(getSymbol('r'),new Pair(new Pair(getSymbol('apply'),new Pair(getSymbol('f'),new Pair(getSymbol('lst'),theNil))),theNil))),theNil)))),theNil))),theNil)))),e,function(list){var r,e=new Env(this.env);while(true){r=((((e.parentEnv['lst'].car)instanceof Pair))!=false?(e.set('o',new Pair(Apply(e.parentEnv['f'],Apply(TopEnv.get('map'),new Pair(TopEnv.get('car'),new Pair(e.parentEnv['lst'],theNil))).ListCopy()),theNil)),(((e.parentEnv['r']==theNil))!=false?e.set('r',e.parentEnv['o']):Apply(TopEnv.get('set-cdr!'),new Pair(e.parentEnv['p'],new Pair(e.parentEnv['o'],theNil)))),e.set('p',e.parentEnv['o']),e.set('lst',Apply(TopEnv.get('map'),new Pair(TopEnv.get('cdr'),new Pair(e.parentEnv['lst'],theNil)))),TC(e.parentEnv['do-map'],list=theNil)):((((e.parentEnv['lst'].car==theNil)==false))!=false?((e.parentEnv['p'])!=false?TC(TopEnv.get('set-cdr!'),list=new Pair(e.parentEnv['p'],new Pair(Apply(e.parentEnv['f'],e.parentEnv['lst'].ListCopy()),theNil))):e.set('r',Apply(e.parentEnv['f'],e.parentEnv['lst'].ListCopy()))):null));if(r!=theTC||r.f!=this)return r}})),function(list){var r,e=new Env(this.env);while(true){e['f']=list.car;e['lst']=list.cdr;r=(e['r']=theNil,e['o']=false,e['p']=false,e['map-lst']=e.parentEnv['_10_'].clone(e),e['do-map']=e.parentEnv['_11_'].clone(e),Apply(e['do-map'],theNil),e['r']);if(r!=theTC||r.f!=this)return r}});
e['caar']=new Lambda(new Pair(getSymbol('x'),theNil),new Pair(getSymbol('car'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('x'),theNil)),theNil)),e,function(list){var r,e=new Env(this.env);while(true){e['x']=list.car;r=e['x'].car.car;if(r!=theTC||r.f!=this)return r}});
e['cadr']=new Lambda(new Pair(getSymbol('x'),theNil),new Pair(getSymbol('car'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('x'),theNil)),theNil)),e,function(list){var r,e=new Env(this.env);while(true){e['x']=list.car;r=e['x'].cdr.car;if(r!=theTC||r.f!=this)return r}});
e['cdar']=new Lambda(new Pair(getSymbol('x'),theNil),new Pair(getSymbol('cdr'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('x'),theNil)),theNil)),e,function(list){var r,e=new Env(this.env);while(true){e['x']=list.car;r=e['x'].car.cdr;if(r!=theTC||r.f!=this)return r}});
e['cddr']=new Lambda(new Pair(getSymbol('x'),theNil),new Pair(getSymbol('cdr'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('x'),theNil)),theNil)),e,function(list){var r,e=new Env(this.env);while(true){e['x']=list.car;r=e['x'].cdr.cdr;if(r!=theTC||r.f!=this)return r}});
e['caaar']=new Lambda(new Pair(getSymbol('x'),theNil),new Pair(getSymbol('car'),new Pair(new Pair(getSymbol('car'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('x'),theNil)),theNil)),theNil)),e,function(list){var r,e=new Env(this.env);while(true){e['x']=list.car;r=e['x'].car.car.car;if(r!=theTC||r.f!=this)return r}});
e['caadr']=new Lambda(new Pair(getSymbol('x'),theNil),new Pair(getSymbol('car'),new Pair(new Pair(getSymbol('car'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('x'),theNil)),theNil)),theNil)),e,function(list){var r,e=new Env(this.env);while(true){e['x']=list.car;r=e['x'].cdr.car.car;if(r!=theTC||r.f!=this)return r}});
e['cadar']=new Lambda(new Pair(getSymbol('x'),theNil),new Pair(getSymbol('car'),new Pair(new Pair(getSymbol('cdr'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('x'),theNil)),theNil)),theNil)),e,function(list){var r,e=new Env(this.env);while(true){e['x']=list.car;r=e['x'].car.cdr.car;if(r!=theTC||r.f!=this)return r}});
e['caddr']=new Lambda(new Pair(getSymbol('x'),theNil),new Pair(getSymbol('car'),new Pair(new Pair(getSymbol('cdr'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('x'),theNil)),theNil)),theNil)),e,function(list){var r,e=new Env(this.env);while(true){e['x']=list.car;r=e['x'].cdr.cdr.car;if(r!=theTC||r.f!=this)return r}});
e['cdaar']=new Lambda(new Pair(getSymbol('x'),theNil),new Pair(getSymbol('cdr'),new Pair(new Pair(getSymbol('car'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('x'),theNil)),theNil)),theNil)),e,function(list){var r,e=new Env(this.env);while(true){e['x']=list.car;r=e['x'].car.car.cdr;if(r!=theTC||r.f!=this)return r}});
e['cdadr']=new Lambda(new Pair(getSymbol('x'),theNil),new Pair(getSymbol('cdr'),new Pair(new Pair(getSymbol('car'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('x'),theNil)),theNil)),theNil)),e,function(list){var r,e=new Env(this.env);while(true){e['x']=list.car;r=e['x'].cdr.car.cdr;if(r!=theTC||r.f!=this)return r}});
e['cddar']=new Lambda(new Pair(getSymbol('x'),theNil),new Pair(getSymbol('cdr'),new Pair(new Pair(getSymbol('cdr'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('x'),theNil)),theNil)),theNil)),e,function(list){var r,e=new Env(this.env);while(true){e['x']=list.car;r=e['x'].car.cdr.cdr;if(r!=theTC||r.f!=this)return r}});
e['cdddr']=new Lambda(new Pair(getSymbol('x'),theNil),new Pair(getSymbol('cdr'),new Pair(new Pair(getSymbol('cdr'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('x'),theNil)),theNil)),theNil)),e,function(list){var r,e=new Env(this.env);while(true){e['x']=list.car;r=e['x'].cdr.cdr.cdr;if(r!=theTC||r.f!=this)return r}});
e['caaddr']=new Lambda(new Pair(getSymbol('x'),theNil),new Pair(getSymbol('car'),new Pair(new Pair(getSymbol('car'),new Pair(new Pair(getSymbol('cdr'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('x'),theNil)),theNil)),theNil)),theNil)),e,function(list){var r,e=new Env(this.env);while(true){e['x']=list.car;r=e['x'].cdr.cdr.car.car;if(r!=theTC||r.f!=this)return r}});
e['cadddr']=new Lambda(new Pair(getSymbol('x'),theNil),new Pair(getSymbol('car'),new Pair(new Pair(getSymbol('cdr'),new Pair(new Pair(getSymbol('cdr'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('x'),theNil)),theNil)),theNil)),theNil)),e,function(list){var r,e=new Env(this.env);while(true){e['x']=list.car;r=e['x'].cdr.cdr.cdr.car;if(r!=theTC||r.f!=this)return r}});
e['cdaddr']=new Lambda(new Pair(getSymbol('x'),theNil),new Pair(getSymbol('cdr'),new Pair(new Pair(getSymbol('car'),new Pair(new Pair(getSymbol('cdr'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('x'),theNil)),theNil)),theNil)),theNil)),e,function(list){var r,e=new Env(this.env);while(true){e['x']=list.car;r=e['x'].cdr.cdr.car.cdr;if(r!=theTC||r.f!=this)return r}});
e['cddddr']=new Lambda(new Pair(getSymbol('x'),theNil),new Pair(getSymbol('cdr'),new Pair(new Pair(getSymbol('cdr'),new Pair(new Pair(getSymbol('cdr'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('x'),theNil)),theNil)),theNil)),theNil)),e,function(list){var r,e=new Env(this.env);while(true){e['x']=list.car;r=e['x'].cdr.cdr.cdr.cdr;if(r!=theTC||r.f!=this)return r}});
e['length']=new Lambda(new Pair(getSymbol('lst'),getSymbol('x')),new Pair(getSymbol('begin'),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('l'),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('null?'),new Pair(getSymbol('x'),theNil)),new Pair(0,new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('x'),theNil)),theNil)))),theNil))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('pair?'),new Pair(getSymbol('lst'),theNil)),new Pair(new Pair(getSymbol('length'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('lst'),theNil)),new Pair(new Pair(getSymbol('+'),new Pair(getSymbol('l'),new Pair(1,theNil))),theNil))),new Pair(getSymbol('l'),theNil)))),theNil))),e,function(list){var r,e=new Env(this.env);while(true){e['lst']=list.car;e['x']=list.cdr;r=(e['l']=(((e['x']==theNil))!=false?0:e['x'].car),((((e['lst'])instanceof Pair))!=false?TC(TopEnv.get('length'),list=new Pair(e['lst'].cdr,new Pair((e['l']+1),theNil))):e['l']));if(r!=theTC||r.f!=this)return r}});
e['length+']=new Lambda(new Pair(getSymbol('lst'),getSymbol('x')),new Pair(getSymbol('begin'),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('l'),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('null?'),new Pair(getSymbol('x'),theNil)),new Pair(0,new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('x'),theNil)),theNil)))),theNil))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('null?'),new Pair(getSymbol('lst'),theNil)),new Pair(getSymbol('l'),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('pair?'),new Pair(getSymbol('lst'),theNil)),new Pair(new Pair(getSymbol('length+'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('lst'),theNil)),new Pair(new Pair(getSymbol('+'),new Pair(getSymbol('l'),new Pair(1,theNil))),theNil))),new Pair(new Pair(getSymbol('+'),new Pair(getSymbol('l'),new Pair(1,theNil))),theNil)))),theNil)))),theNil))),e,function(list){var r,e=new Env(this.env);while(true){e['lst']=list.car;e['x']=list.cdr;r=(e['l']=(((e['x']==theNil))!=false?0:e['x'].car),(((e['lst']==theNil))!=false?e['l']:((((e['lst'])instanceof Pair))!=false?TC(TopEnv.get('length+'),list=new Pair(e['lst'].cdr,new Pair((e['l']+1),theNil))):(e['l']+1))));if(r!=theTC||r.f!=this)return r}});
e['list-ref']=new Lambda(new Pair(getSymbol('lst'),new Pair(getSymbol('n'),theNil)),new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('='),new Pair(getSymbol('n'),new Pair(0,theNil))),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('lst'),theNil)),new Pair(new Pair(getSymbol('list-ref'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('lst'),theNil)),new Pair(new Pair(getSymbol('-'),new Pair(getSymbol('n'),new Pair(1,theNil))),theNil))),theNil)))),e,function(list){var r,e=new Env(this.env);while(true){e['lst']=list.car;e['n']=list.cdr.car;r=((isEq(e['n'],0))!=false?e['lst'].car:TC(TopEnv.get('list-ref'),list=new Pair(e['lst'].cdr,new Pair((e['n']-1),theNil))));if(r!=theTC||r.f!=this)return r}});
e['list-tail']=new Lambda(new Pair(getSymbol('lst'),new Pair(getSymbol('n'),theNil)),new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('='),new Pair(getSymbol('n'),new Pair(0,theNil))),new Pair(getSymbol('lst'),new Pair(new Pair(getSymbol('list-tail'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('lst'),theNil)),new Pair(new Pair(getSymbol('-'),new Pair(getSymbol('n'),new Pair(1,theNil))),theNil))),theNil)))),e,function(list){var r,e=new Env(this.env);while(true){e['lst']=list.car;e['n']=list.cdr.car;r=((isEq(e['n'],0))!=false?e['lst']:TC(TopEnv.get('list-tail'),list=new Pair(e['lst'].cdr,new Pair((e['n']-1),theNil))));if(r!=theTC||r.f!=this)return r}});
e['reverse']=new Lambda(new Pair(getSymbol('lst'),getSymbol('l2')),new Pair(getSymbol('begin'),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('r'),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('null?'),new Pair(getSymbol('l2'),theNil)),new Pair(getSymbol('l2'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('l2'),theNil)),theNil)))),theNil))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('null?'),new Pair(getSymbol('lst'),theNil)),new Pair(getSymbol('r'),new Pair(new Pair(getSymbol('reverse'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('lst'),theNil)),new Pair(new Pair(getSymbol('cons'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('lst'),theNil)),new Pair(getSymbol('r'),theNil))),theNil))),theNil)))),theNil))),e,function(list){var r,e=new Env(this.env);while(true){e['lst']=list.car;e['l2']=list.cdr;r=(e['r']=(((e['l2']==theNil))!=false?e['l2']:e['l2'].car),(((e['lst']==theNil))!=false?e['r']:TC(TopEnv.get('reverse'),list=new Pair(e['lst'].cdr,new Pair(new Pair(e['lst'].car,e['r']),theNil)))));if(r!=theTC||r.f!=this)return r}});
e['append']=new Lambda(new Pair(getSymbol('l1'),getSymbol('more')),new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('null?'),new Pair(getSymbol('more'),theNil)),new Pair(getSymbol('l1'),new Pair(new Pair(getSymbol('begin'),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('l2'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('more'),theNil)),theNil))),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('m2'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('more'),theNil)),theNil))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('null?'),new Pair(getSymbol('l1'),theNil)),new Pair(new Pair(getSymbol('apply'),new Pair(getSymbol('append'),new Pair(getSymbol('l2'),new Pair(getSymbol('m2'),theNil)))),new Pair(new Pair(getSymbol('cons'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('l1'),theNil)),new Pair(new Pair(getSymbol('apply'),new Pair(getSymbol('append'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('l1'),theNil)),new Pair(getSymbol('l2'),new Pair(getSymbol('m2'),theNil))))),theNil))),theNil)))),theNil)))),theNil)))),e,function(list){var r,e=new Env(this.env);while(true){e['l1']=list.car;e['more']=list.cdr;r=(((e['more']==theNil))!=false?e['l1']:(e['l2']=e['more'].car,e['m2']=e['more'].cdr,(((e['l1']==theNil))!=false?TC(TopEnv.get('append'),list=new Pair(e['l2'],e['m2'].ListCopy())):new Pair(e['l1'].car,Apply(TopEnv.get('append'),new Pair(e['l1'].cdr,new Pair(e['l2'],e['m2'].ListCopy())))))));if(r!=theTC||r.f!=this)return r}});
e['sort']=false;
e['merge']=false;
Apply(new Lambda(theNil,new Pair(getSymbol('begin'),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('dosort'),new Pair(new Pair(getSymbol('clone'),new Pair(getSymbol('_12_'),theNil)),theNil))),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('domerge'),new Pair(new Pair(getSymbol('clone'),new Pair(getSymbol('_13_'),theNil)),theNil))),new Pair(new Pair(getSymbol('set!'),new Pair(getSymbol('sort'),new Pair(new Pair(getSymbol('clone'),new Pair(getSymbol('_14_'),theNil)),theNil))),new Pair(new Pair(getSymbol('set!'),new Pair(getSymbol('merge'),new Pair(new Pair(getSymbol('clone'),new Pair(getSymbol('_15_'),theNil)),theNil))),theNil))))),new Env(e).With('_12_',new Lambda(new Pair(getSymbol('pred?'),new Pair(getSymbol('ls'),new Pair(getSymbol('n'),theNil))),new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('='),new Pair(getSymbol('n'),new Pair(1,theNil))),new Pair(new Pair(getSymbol('list'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ls'),theNil)),theNil)),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('='),new Pair(getSymbol('n'),new Pair(2,theNil))),new Pair(new Pair(getSymbol('begin'),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('x'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ls'),theNil)),theNil))),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('y'),new Pair(new Pair(getSymbol('cadr'),new Pair(getSymbol('ls'),theNil)),theNil))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('pred?'),new Pair(getSymbol('y'),new Pair(getSymbol('x'),theNil))),new Pair(new Pair(getSymbol('list'),new Pair(getSymbol('y'),new Pair(getSymbol('x'),theNil))),new Pair(new Pair(getSymbol('list'),new Pair(getSymbol('x'),new Pair(getSymbol('y'),theNil))),theNil)))),theNil)))),new Pair(new Pair(getSymbol('begin'),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('i'),new Pair(new Pair(getSymbol('quotient'),new Pair(getSymbol('n'),new Pair(2,theNil))),theNil))),new Pair(new Pair(getSymbol('domerge'),new Pair(getSymbol('pred?'),new Pair(new Pair(getSymbol('dosort'),new Pair(getSymbol('pred?'),new Pair(getSymbol('ls'),new Pair(getSymbol('i'),theNil)))),new Pair(new Pair(getSymbol('dosort'),new Pair(getSymbol('pred?'),new Pair(new Pair(getSymbol('list-tail'),new Pair(getSymbol('ls'),new Pair(getSymbol('i'),theNil))),new Pair(new Pair(getSymbol('-'),new Pair(getSymbol('n'),new Pair(getSymbol('i'),theNil))),theNil)))),theNil)))),theNil))),theNil)))),theNil)))),e,function(list){var r,e=new Env(this.env);while(true){e['pred?']=list.car;e['ls']=list.cdr.car;e['n']=list.cdr.cdr.car;r=((isEq(e['n'],1))!=false?new Pair(e['ls'].car,theNil):((isEq(e['n'],2))!=false?(e['x']=e['ls'].car,e['y']=e['ls'].cdr.car,((Apply(e['pred?'],new Pair(e['y'],new Pair(e['x'],theNil))))!=false?new Pair(e['y'],new Pair(e['x'],theNil)):new Pair(e['x'],new Pair(e['y'],theNil)))):(e['i']=Apply(TopEnv.get('quotient'),new Pair(e['n'],new Pair(2,theNil))),TC(e.parentEnv['domerge'],list=new Pair(e['pred?'],new Pair(Apply(e.parentEnv['dosort'],new Pair(e['pred?'],new Pair(e['ls'],new Pair(e['i'],theNil)))),new Pair(Apply(e.parentEnv['dosort'],new Pair(e['pred?'],new Pair(Apply(TopEnv.get('list-tail'),new Pair(e['ls'],new Pair(e['i'],theNil))),new Pair((e['n']-e['i']),theNil)))),theNil)))))));if(r!=theTC||r.f!=this)return r}})).With('_13_',new Lambda(new Pair(getSymbol('pred?'),new Pair(getSymbol('l1'),new Pair(getSymbol('l2'),theNil))),new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('null?'),new Pair(getSymbol('l1'),theNil)),new Pair(getSymbol('l2'),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('null?'),new Pair(getSymbol('l2'),theNil)),new Pair(getSymbol('l1'),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('pred?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('l2'),theNil)),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('l1'),theNil)),theNil))),new Pair(new Pair(getSymbol('cons'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('l2'),theNil)),new Pair(new Pair(getSymbol('domerge'),new Pair(getSymbol('pred?'),new Pair(getSymbol('l1'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('l2'),theNil)),theNil)))),theNil))),new Pair(new Pair(getSymbol('cons'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('l1'),theNil)),new Pair(new Pair(getSymbol('domerge'),new Pair(getSymbol('pred?'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('l1'),theNil)),new Pair(getSymbol('l2'),theNil)))),theNil))),theNil)))),theNil)))),theNil)))),e,function(list){var r,e=new Env(this.env);while(true){e['pred?']=list.car;e['l1']=list.cdr.car;e['l2']=list.cdr.cdr.car;r=(((e['l1']==theNil))!=false?e['l2']:(((e['l2']==theNil))!=false?e['l1']:((Apply(e['pred?'],new Pair(e['l2'].car,new Pair(e['l1'].car,theNil))))!=false?new Pair(e['l2'].car,Apply(e.parentEnv['domerge'],new Pair(e['pred?'],new Pair(e['l1'],new Pair(e['l2'].cdr,theNil))))):new Pair(e['l1'].car,Apply(e.parentEnv['domerge'],new Pair(e['pred?'],new Pair(e['l1'].cdr,new Pair(e['l2'],theNil))))))));if(r!=theTC||r.f!=this)return r}})).With('_14_',new Lambda(new Pair(getSymbol('pred?'),new Pair(getSymbol('l'),theNil)),new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('null?'),new Pair(getSymbol('l'),theNil)),new Pair(getSymbol('l'),new Pair(new Pair(getSymbol('dosort'),new Pair(getSymbol('pred?'),new Pair(getSymbol('l'),new Pair(new Pair(getSymbol('length'),new Pair(getSymbol('l'),theNil)),theNil)))),theNil)))),e,function(list){var r,e=new Env(this.env);while(true){e['pred?']=list.car;e['l']=list.cdr.car;r=(((e['l']==theNil))!=false?e['l']:TC(e.parentEnv['dosort'],list=new Pair(e['pred?'],new Pair(e['l'],new Pair(Apply(TopEnv.get('length'),new Pair(e['l'],theNil)),theNil)))));if(r!=theTC||r.f!=this)return r}})).With('_15_',new Lambda(new Pair(getSymbol('pred?'),new Pair(getSymbol('l1'),new Pair(getSymbol('l2'),theNil))),new Pair(getSymbol('domerge'),new Pair(getSymbol('pred?'),new Pair(getSymbol('l1'),new Pair(getSymbol('l2'),theNil)))),e,function(list){var r,e=new Env(this.env);while(true){e['pred?']=list.car;e['l1']=list.cdr.car;e['l2']=list.cdr.cdr.car;r=TC(e.parentEnv['domerge'],list=new Pair(e['pred?'],new Pair(e['l1'],new Pair(e['l2'],theNil))));if(r!=theTC||r.f!=this)return r}})),function(list){var r,e=new Env(this.env);while(true){r=(e['dosort']=e.parentEnv['_12_'].clone(e),e['domerge']=e.parentEnv['_13_'].clone(e),e.set('sort',e.parentEnv['_14_'].clone(e)),e.set('merge',e.parentEnv['_15_'].clone(e)));if(r!=theTC||r.f!=this)return r}}),theNil);
e['iota']=new Lambda(new Pair(getSymbol('count'),getSymbol('x')),new Pair(getSymbol('begin'),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('start'),new Pair(0,theNil))),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('step'),new Pair(1,theNil))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('not'),new Pair(new Pair(getSymbol('null?'),new Pair(getSymbol('x'),theNil)),theNil)),new Pair(new Pair(getSymbol('begin'),new Pair(new Pair(getSymbol('set!'),new Pair(getSymbol('start'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('x'),theNil)),theNil))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('not'),new Pair(new Pair(getSymbol('null?'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('x'),theNil)),theNil)),theNil)),new Pair(new Pair(getSymbol('begin'),new Pair(new Pair(getSymbol('set!'),new Pair(getSymbol('step'),new Pair(new Pair(getSymbol('cadr'),new Pair(getSymbol('x'),theNil)),theNil))),theNil)),theNil))),theNil))),theNil))),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('do-step'),new Pair(new Pair(getSymbol('clone'),new Pair(getSymbol('_16_'),theNil)),theNil))),new Pair(new Pair(getSymbol('do-step'),new Pair(new Pair(getSymbol('-'),new Pair(getSymbol('count'),new Pair(1,theNil))),new Pair(new Pair(getSymbol('quote'),new Pair(theNil,theNil)),theNil))),theNil)))))),new Env(e).With('_16_',new Lambda(new Pair(getSymbol('cnt'),new Pair(getSymbol('lst'),theNil)),new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('<'),new Pair(getSymbol('cnt'),new Pair(0,theNil))),new Pair(getSymbol('lst'),new Pair(new Pair(getSymbol('do-step'),new Pair(new Pair(getSymbol('-'),new Pair(getSymbol('cnt'),new Pair(1,theNil))),new Pair(new Pair(getSymbol('cons'),new Pair(new Pair(getSymbol('+'),new Pair(new Pair(getSymbol('*'),new Pair(getSymbol('step'),new Pair(getSymbol('cnt'),theNil))),new Pair(getSymbol('start'),theNil))),new Pair(getSymbol('lst'),theNil))),theNil))),theNil)))),e,function(list){var r,e=new Env(this.env);while(true){e['cnt']=list.car;e['lst']=list.cdr.car;r=((e['cnt']<0)!=false?e['lst']:TC(e.parentEnv['do-step'],list=new Pair((e['cnt']-1),new Pair(new Pair(((e.parentEnv['step']*e['cnt'])+e.parentEnv['start']),e['lst']),theNil))));if(r!=theTC||r.f!=this)return r}})),function(list){var r,e=new Env(this.env);while(true){e['count']=list.car;e['x']=list.cdr;r=(e['start']=0,e['step']=1,((((e['x']==theNil)==false))!=false?(e['start']=e['x'].car,((((e['x'].cdr==theNil)==false))!=false?e['step']=e['x'].cdr.car:null)):null),e['do-step']=e.parentEnv['_16_'].clone(e),TC(e['do-step'],list=new Pair((e['count']-1),new Pair(theNil,theNil))));if(r!=theTC||r.f!=this)return r}});
e['list->string']=new Lambda(new Pair(getSymbol('lst'),theNil),new Pair(getSymbol('apply'),new Pair(getSymbol('string'),new Pair(getSymbol('lst'),theNil))),e,function(list){var r,e=new Env(this.env);while(true){e['lst']=list.car;r=TC(TopEnv.get('string'),list=e['lst'].ListCopy());if(r!=theTC||r.f!=this)return r}});
e['gcd']=new Lambda(new Pair(getSymbol('a'),new Pair(getSymbol('b'),theNil)),new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('='),new Pair(getSymbol('b'),new Pair(0,theNil))),new Pair(getSymbol('a'),new Pair(new Pair(getSymbol('gcd'),new Pair(getSymbol('b'),new Pair(new Pair(getSymbol('remainder'),new Pair(getSymbol('a'),new Pair(getSymbol('b'),theNil))),theNil))),theNil)))),e,function(list){var r,e=new Env(this.env);while(true){e['a']=list.car;e['b']=list.cdr.car;r=((isEq(e['b'],0))!=false?e['a']:TC(TopEnv.get('gcd'),list=new Pair(e['b'],new Pair(Apply(TopEnv.get('remainder'),new Pair(e['a'],new Pair(e['b'],theNil))),theNil))));if(r!=theTC||r.f!=this)return r}});
e['lcm']=new Lambda(new Pair(getSymbol('x'),new Pair(getSymbol('y'),theNil)),new Pair(getSymbol('/'),new Pair(new Pair(getSymbol('*'),new Pair(getSymbol('x'),new Pair(getSymbol('y'),theNil))),new Pair(new Pair(getSymbol('gcd'),new Pair(getSymbol('x'),new Pair(getSymbol('y'),theNil))),theNil))),e,function(list){var r,e=new Env(this.env);while(true){e['x']=list.car;e['y']=list.cdr.car;r=((e['x']*e['y'])/Apply(TopEnv.get('gcd'),new Pair(e['x'],new Pair(e['y'],theNil))));if(r!=theTC||r.f!=this)return r}});
e['max']=new Lambda(new Pair(getSymbol('x'),getSymbol('l')),new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('null?'),new Pair(getSymbol('l'),theNil)),new Pair(getSymbol('x'),new Pair(new Pair(getSymbol('apply'),new Pair(getSymbol('max'),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('>'),new Pair(getSymbol('x'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('l'),theNil)),theNil))),new Pair(getSymbol('x'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('l'),theNil)),theNil)))),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('l'),theNil)),theNil)))),theNil)))),e,function(list){var r,e=new Env(this.env);while(true){e['x']=list.car;e['l']=list.cdr;r=(((e['l']==theNil))!=false?e['x']:TC(TopEnv.get('max'),list=new Pair(((e['x']>e['l'].car)!=false?e['x']:e['l'].car),e['l'].cdr.ListCopy())));if(r!=theTC||r.f!=this)return r}});
e['min']=new Lambda(new Pair(getSymbol('x'),getSymbol('l')),new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('null?'),new Pair(getSymbol('l'),theNil)),new Pair(getSymbol('x'),new Pair(new Pair(getSymbol('apply'),new Pair(getSymbol('max'),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('<'),new Pair(getSymbol('x'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('l'),theNil)),theNil))),new Pair(getSymbol('x'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('l'),theNil)),theNil)))),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('l'),theNil)),theNil)))),theNil)))),e,function(list){var r,e=new Env(this.env);while(true){e['x']=list.car;e['l']=list.cdr;r=(((e['l']==theNil))!=false?e['x']:TC(TopEnv.get('max'),list=new Pair(((e['x']<e['l'].car)!=false?e['x']:e['l'].car),e['l'].cdr.ListCopy())));if(r!=theTC||r.f!=this)return r}});
e['syntax-quasiquote']=Apply(new Lambda(theNil,new Pair(getSymbol('begin'),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('ql'),new Pair(new Pair(getSymbol('clone'),new Pair(getSymbol('_17_'),theNil)),theNil))),new Pair(new Pair(getSymbol('clone'),new Pair(getSymbol('_18_'),theNil)),theNil))),new Env(e).With('_17_',new Lambda(new Pair(getSymbol('x'),theNil),new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('pair?'),new Pair(getSymbol('x'),theNil)),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('null?'),new Pair(getSymbol('x'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(new Pair(getSymbol('quote'),new Pair(theNil,theNil)),theNil)),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eq?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('x'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('unquote'),theNil)),theNil))),new Pair(new Pair(getSymbol('cadr'),new Pair(getSymbol('x'),theNil)),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('pair?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('x'),theNil)),theNil)),new Pair(new Pair(getSymbol('eq?'),new Pair(new Pair(getSymbol('caar'),new Pair(getSymbol('x'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('unquote-splicing'),theNil)),theNil))),new Pair(false,theNil)))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('null?'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('x'),theNil)),theNil)),new Pair(new Pair(getSymbol('cadar'),new Pair(getSymbol('x'),theNil)),new Pair(new Pair(getSymbol('list'),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('append'),theNil)),new Pair(new Pair(getSymbol('cadar'),new Pair(getSymbol('x'),theNil)),new Pair(new Pair(getSymbol('ql'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('x'),theNil)),theNil)),theNil)))),theNil)))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('null?'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('x'),theNil)),theNil)),new Pair(new Pair(getSymbol('list'),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('list'),theNil)),new Pair(new Pair(getSymbol('ql'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('x'),theNil)),theNil)),theNil))),new Pair(new Pair(getSymbol('list'),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('cons'),theNil)),new Pair(new Pair(getSymbol('ql'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('x'),theNil)),theNil)),new Pair(new Pair(getSymbol('ql'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('x'),theNil)),theNil)),theNil)))),theNil)))),theNil)))),theNil)))),theNil)))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('symbol?'),new Pair(getSymbol('x'),theNil)),new Pair(new Pair(getSymbol('list'),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('quote'),theNil)),new Pair(getSymbol('x'),theNil))),new Pair(getSymbol('x'),theNil)))),theNil)))),e,function(list){var r,e=new Env(this.env);while(true){e['x']=list.car;r=((((e['x'])instanceof Pair))!=false?(((e['x']==theNil))!=false?new Pair(getSymbol('quote'),new Pair(theNil,theNil)):((isEq(e['x'].car,getSymbol('unquote')))!=false?e['x'].cdr.car:((((((e['x'].car)instanceof Pair))!=false?isEq(e['x'].car.car,getSymbol('unquote-splicing')):false))!=false?(((e['x'].cdr==theNil))!=false?TC(TopEnv.get('cadar'),list=new Pair(e['x'],theNil)):new Pair(getSymbol('append'),new Pair(Apply(TopEnv.get('cadar'),new Pair(e['x'],theNil)),new Pair(Apply(e.parentEnv['ql'],new Pair(e['x'].cdr,theNil)),theNil)))):(((e['x'].cdr==theNil))!=false?new Pair(getSymbol('list'),new Pair(Apply(e.parentEnv['ql'],new Pair(e['x'].car,theNil)),theNil)):new Pair(getSymbol('cons'),new Pair(Apply(e.parentEnv['ql'],new Pair(e['x'].car,theNil)),new Pair(Apply(e.parentEnv['ql'],new Pair(e['x'].cdr,theNil)),theNil))))))):((((e['x'])instanceof Symbol))!=false?new Pair(getSymbol('quote'),new Pair(e['x'],theNil)):e['x']));if(r!=theTC||r.f!=this)return r}})).With('_18_',new Lambda(new Pair(getSymbol('expr'),theNil),new Pair(getSymbol('ql'),new Pair(new Pair(getSymbol('cadr'),new Pair(getSymbol('expr'),theNil)),theNil)),e,function(list){var r,e=new Env(this.env);while(true){e['expr']=list.car;r=TC(e.parentEnv['ql'],list=new Pair(e['expr'].cdr.car,theNil));if(r!=theTC||r.f!=this)return r}})),function(list){var r,e=new Env(this.env);while(true){r=(e['ql']=e.parentEnv['_17_'].clone(e),e.parentEnv['_18_'].clone(e));if(r!=theTC||r.f!=this)return r}}),theNil);
e['quasiquote']=new Syntax(e.get('syntax-quasiquote'),theNil);
e['f-and']=new Lambda(getSymbol('lst'),new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('null?'),new Pair(getSymbol('lst'),theNil)),new Pair(true,new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('lst'),theNil)),new Pair(new Pair(getSymbol('apply'),new Pair(getSymbol('f-and'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('lst'),theNil)),theNil))),new Pair(false,theNil)))),theNil)))),e,function(list){var r,e=new Env(this.env);while(true){e['lst']=list;r=(((e['lst']==theNil))!=false?true:((e['lst'].car)!=false?TC(TopEnv.get('f-and'),list=e['lst'].cdr.ListCopy()):false));if(r!=theTC||r.f!=this)return r}});
e['f-or']=new Lambda(getSymbol('lst'),new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('null?'),new Pair(getSymbol('lst'),theNil)),new Pair(false,new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('lst'),theNil)),new Pair(true,new Pair(new Pair(getSymbol('apply'),new Pair(getSymbol('f-or'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('lst'),theNil)),theNil))),theNil)))),theNil)))),e,function(list){var r,e=new Env(this.env);while(true){e['lst']=list;r=(((e['lst']==theNil))!=false?false:((e['lst'].car)!=false?true:TC(TopEnv.get('f-or'),list=e['lst'].cdr.ListCopy())));if(r!=theTC||r.f!=this)return r}});
e['syntax-rules']=new Lambda(new Pair(getSymbol('expr'),new Pair(getSymbol('literals'),new Pair(getSymbol('p1'),getSymbol('more')))),new Pair(getSymbol('begin'),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('vars'),new Pair(new Pair(getSymbol('quote'),new Pair(theNil,theNil)),theNil))),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('match'),new Pair(new Pair(getSymbol('clone'),new Pair(getSymbol('_19_'),theNil)),theNil))),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('match-many'),new Pair(new Pair(getSymbol('clone'),new Pair(getSymbol('_20_'),theNil)),theNil))),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('find-all'),new Pair(new Pair(getSymbol('clone'),new Pair(getSymbol('_21_'),theNil)),theNil))),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('p-each'),new Pair(new Pair(getSymbol('clone'),new Pair(getSymbol('_22_'),theNil)),theNil))),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('process-many'),new Pair(new Pair(getSymbol('clone'),new Pair(getSymbol('_23_'),theNil)),theNil))),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('gen-many'),new Pair(new Pair(getSymbol('clone'),new Pair(getSymbol('_24_'),theNil)),theNil))),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('ren'),new Pair(new Pair(getSymbol('clone'),new Pair(getSymbol('_25_'),theNil)),theNil))),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('gen'),new Pair(new Pair(getSymbol('clone'),new Pair(getSymbol('_26_'),theNil)),theNil))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('match'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('expr'),theNil)),new Pair(new Pair(getSymbol('cdar'),new Pair(getSymbol('p1'),theNil)),theNil))),new Pair(new Pair(getSymbol('gen'),new Pair(new Pair(getSymbol('cadr'),new Pair(getSymbol('p1'),theNil)),new Pair(true,theNil))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('null?'),new Pair(getSymbol('more'),theNil)),new Pair(new Pair(getSymbol('error'),new Pair(new Pair(getSymbol('string-append'),new Pair("no pattern matches ",new Pair(new Pair(getSymbol('symbol->string'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('expr'),theNil)),theNil)),theNil))),theNil)),new Pair(new Pair(getSymbol('apply'),new Pair(getSymbol('syntax-rules'),new Pair(getSymbol('expr'),new Pair(getSymbol('literals'),new Pair(getSymbol('more'),theNil))))),theNil)))),theNil)))),theNil))))))))))),new Env(e).With('_19_',new Lambda(new Pair(getSymbol('ex'),new Pair(getSymbol('pat'),theNil)),new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('null?'),new Pair(getSymbol('pat'),theNil)),new Pair(new Pair(getSymbol('null?'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('symbol?'),new Pair(getSymbol('pat'),theNil)),new Pair(new Pair(getSymbol('begin'),new Pair(new Pair(getSymbol('set!'),new Pair(getSymbol('vars'),new Pair(new Pair(getSymbol('cons'),new Pair(new Pair(getSymbol('cons'),new Pair(getSymbol('pat'),new Pair(getSymbol('ex'),theNil))),new Pair(getSymbol('vars'),theNil))),theNil))),new Pair(true,theNil))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eq?'),new Pair(new Pair(getSymbol('cadr'),new Pair(getSymbol('pat'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('...'),theNil)),theNil))),new Pair(new Pair(getSymbol('match-many'),new Pair(getSymbol('ex'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('pat'),theNil)),theNil))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('null?'),new Pair(getSymbol('ex'),theNil)),new Pair(false,new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('memq+'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('pat'),theNil)),new Pair(getSymbol('literals'),theNil))),new Pair(new Pair(getSymbol('eq?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('pat'),theNil)),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),theNil))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('symbol?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('pat'),theNil)),theNil)),new Pair(new Pair(getSymbol('begin'),new Pair(new Pair(getSymbol('set!'),new Pair(getSymbol('vars'),new Pair(new Pair(getSymbol('cons'),new Pair(new Pair(getSymbol('cons'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('pat'),theNil)),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),theNil))),new Pair(getSymbol('vars'),theNil))),theNil))),new Pair(true,theNil))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('pair?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('pat'),theNil)),theNil)),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('null?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),theNil)),new Pair(true,new Pair(new Pair(getSymbol('pair?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),theNil)),theNil)))),new Pair(false,theNil)))),new Pair(new Pair(getSymbol('match'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('pat'),theNil)),theNil))),new Pair(new Pair(getSymbol('eqv?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('pat'),theNil)),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),theNil))),theNil)))),theNil)))),theNil)))),theNil)))),new Pair(new Pair(getSymbol('match'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('pat'),theNil)),theNil))),new Pair(false,theNil)))),theNil)))),theNil)))),theNil)))),e,function(list){var r,e=new Env(this.env);while(true){e['ex']=list.car;e['pat']=list.cdr.car;r=(((e['pat']==theNil))!=false?(e['ex']==theNil):((((e['pat'])instanceof Symbol))!=false?(e.set('vars',new Pair(new Pair(e['pat'],e['ex']),e.parentEnv['vars'])),true):((isEq(e['pat'].cdr.car,getSymbol('...')))!=false?TC(e.parentEnv['match-many'],list=new Pair(e['ex'],new Pair(e['pat'].car,theNil))):(((((e['ex']==theNil))!=false?false:((Apply(TopEnv.get('memq+'),new Pair(e['pat'].car,new Pair(e.parentEnv['literals'],theNil))))!=false?isEq(e['pat'].car,e['ex'].car):((((e['pat'].car)instanceof Symbol))!=false?(e.set('vars',new Pair(new Pair(e['pat'].car,e['ex'].car),e.parentEnv['vars'])),true):((((((e['pat'].car)instanceof Pair))!=false?(((e['ex'].car==theNil))!=false?true:((e['ex'].car)instanceof Pair)):false))!=false?Apply(e.parentEnv['match'],new Pair(e['ex'].car,new Pair(e['pat'].car,theNil))):isEq(e['pat'].car,e['ex'].car))))))!=false?TC(e.parentEnv['match'],list=new Pair(e['ex'].cdr,new Pair(e['pat'].cdr,theNil))):false))));if(r!=theTC||r.f!=this)return r}})).With('_20_',new Lambda(new Pair(getSymbol('ex'),new Pair(getSymbol('pat'),theNil)),new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('null?'),new Pair(getSymbol('ex'),theNil)),new Pair(true,new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('match'),new Pair(new Pair(getSymbol('list'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),theNil)),new Pair(new Pair(getSymbol('list'),new Pair(getSymbol('pat'),theNil)),theNil))),new Pair(new Pair(getSymbol('match-many'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('ex'),theNil)),new Pair(getSymbol('pat'),theNil))),new Pair(false,theNil)))),theNil)))),e,function(list){var r,e=new Env(this.env);while(true){e['ex']=list.car;e['pat']=list.cdr.car;r=(((e['ex']==theNil))!=false?true:((Apply(e.parentEnv['match'],new Pair(new Pair(e['ex'].car,theNil),new Pair(new Pair(e['pat'],theNil),theNil))))!=false?TC(e.parentEnv['match-many'],list=new Pair(e['ex'].cdr,new Pair(e['pat'],theNil))):false));if(r!=theTC||r.f!=this)return r}})).With('_21_',new Lambda(new Pair(getSymbol('var'),new Pair(getSymbol('lst'),new Pair(getSymbol('out'),theNil))),new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('null?'),new Pair(getSymbol('lst'),theNil)),new Pair(getSymbol('out'),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eq?'),new Pair(getSymbol('var'),new Pair(new Pair(getSymbol('caar'),new Pair(getSymbol('lst'),theNil)),theNil))),new Pair(new Pair(getSymbol('find-all'),new Pair(getSymbol('var'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('lst'),theNil)),new Pair(new Pair(getSymbol('cons'),new Pair(new Pair(getSymbol('cdar'),new Pair(getSymbol('lst'),theNil)),new Pair(getSymbol('out'),theNil))),theNil)))),new Pair(new Pair(getSymbol('find-all'),new Pair(getSymbol('var'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('lst'),theNil)),new Pair(getSymbol('out'),theNil)))),theNil)))),theNil)))),e,function(list){var r,e=new Env(this.env);while(true){e['var']=list.car;e['lst']=list.cdr.car;e['out']=list.cdr.cdr.car;r=(((e['lst']==theNil))!=false?e['out']:((isEq(e['var'],e['lst'].car.car))!=false?TC(e.parentEnv['find-all'],list=new Pair(e['var'],new Pair(e['lst'].cdr,new Pair(new Pair(e['lst'].car.cdr,e['out']),theNil)))):TC(e.parentEnv['find-all'],list=new Pair(e['var'],new Pair(e['lst'].cdr,new Pair(e['out'],theNil))))));if(r!=theTC||r.f!=this)return r}})).With('_22_',new Lambda(new Pair(getSymbol('lst'),new Pair(getSymbol('templ'),theNil)),new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('null?'),new Pair(getSymbol('lst'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(theNil,theNil)),new Pair(new Pair(getSymbol('cons'),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('null?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('lst'),theNil)),theNil)),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('templ'),theNil)),new Pair(new Pair(getSymbol('caar'),new Pair(getSymbol('lst'),theNil)),theNil)))),new Pair(new Pair(getSymbol('p-each'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('lst'),theNil)),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('templ'),theNil)),theNil))),theNil))),theNil)))),e,function(list){var r,e=new Env(this.env);while(true){e['lst']=list.car;e['templ']=list.cdr.car;r=(((e['lst']==theNil))!=false?theNil:new Pair((((e['lst'].car==theNil))!=false?e['templ'].car:e['lst'].car.car),Apply(e.parentEnv['p-each'],new Pair(e['lst'].cdr,new Pair(e['templ'].cdr,theNil)))));if(r!=theTC||r.f!=this)return r}})).With('_23_',new Lambda(new Pair(getSymbol('lst'),new Pair(getSymbol('templ'),theNil)),new Pair(getSymbol('begin'),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('not-empty'),new Pair(false,theNil))),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('l2'),new Pair(new Pair(getSymbol('clone'),new Pair(getSymbol('_27_'),theNil)),theNil))),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('ll'),new Pair(new Pair(getSymbol('l2'),new Pair(getSymbol('lst'),theNil)),theNil))),new Pair(new Pair(getSymbol('if'),new Pair(getSymbol('not-empty'),new Pair(new Pair(getSymbol('cons'),new Pair(new Pair(getSymbol('p-each'),new Pair(getSymbol('lst'),new Pair(getSymbol('templ'),theNil))),new Pair(new Pair(getSymbol('process-many'),new Pair(getSymbol('ll'),new Pair(getSymbol('templ'),theNil))),theNil))),new Pair(new Pair(getSymbol('quote'),new Pair(theNil,theNil)),theNil)))),theNil))))),new Env(e).With('_27_',new Lambda(new Pair(getSymbol('l'),theNil),new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('null?'),new Pair(getSymbol('l'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(theNil,theNil)),new Pair(new Pair(getSymbol('begin'),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('a'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('l'),theNil)),theNil))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('not'),new Pair(new Pair(getSymbol('null?'),new Pair(getSymbol('a'),theNil)),theNil)),new Pair(new Pair(getSymbol('begin'),new Pair(new Pair(getSymbol('set!'),new Pair(getSymbol('not-empty'),new Pair(true,theNil))),new Pair(new Pair(getSymbol('set!'),new Pair(getSymbol('a'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('a'),theNil)),theNil))),theNil))),theNil))),new Pair(new Pair(getSymbol('cons'),new Pair(getSymbol('a'),new Pair(new Pair(getSymbol('l2'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('l'),theNil)),theNil)),theNil))),theNil)))),theNil)))),e,function(list){var r,e=new Env(this.env);while(true){e['l']=list.car;r=(((e['l']==theNil))!=false?theNil:(e['a']=e['l'].car,((((e['a']==theNil)==false))!=false?(e.set('not-empty',true),e['a']=e['a'].cdr):null),new Pair(e['a'],Apply(e.parentEnv['l2'],new Pair(e['l'].cdr,theNil)))));if(r!=theTC||r.f!=this)return r}})),function(list){var r,e=new Env(this.env);while(true){e['lst']=list.car;e['templ']=list.cdr.car;r=(e['not-empty']=false,e['l2']=e.parentEnv['_27_'].clone(e),e['ll']=Apply(e['l2'],new Pair(e['lst'],theNil)),((e['not-empty'])!=false?new Pair(Apply(e.parentEnv.parentEnv['p-each'],new Pair(e['lst'],new Pair(e['templ'],theNil))),Apply(e.parentEnv.parentEnv['process-many'],new Pair(e['ll'],new Pair(e['templ'],theNil)))):theNil));if(r!=theTC||r.f!=this)return r}})).With('_24_',new Lambda(new Pair(getSymbol('templ'),theNil),new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('null?'),new Pair(getSymbol('templ'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(theNil,theNil)),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('pair?'),new Pair(getSymbol('templ'),theNil)),new Pair(new Pair(getSymbol('process-many'),new Pair(new Pair(getSymbol('map+'),new Pair(getSymbol('gen-many'),new Pair(getSymbol('templ'),theNil))),new Pair(getSymbol('templ'),theNil))),new Pair(new Pair(getSymbol('find-all'),new Pair(getSymbol('templ'),new Pair(getSymbol('vars'),new Pair(new Pair(getSymbol('quote'),new Pair(theNil,theNil)),theNil)))),theNil)))),theNil)))),e,function(list){var r,e=new Env(this.env);while(true){e['templ']=list.car;r=(((e['templ']==theNil))!=false?theNil:((((e['templ'])instanceof Pair))!=false?TC(e.parentEnv['process-many'],list=new Pair(Apply(TopEnv.get('map+'),new Pair(e.parentEnv['gen-many'],new Pair(e['templ'],theNil))),new Pair(e['templ'],theNil))):TC(e.parentEnv['find-all'],list=new Pair(e['templ'],new Pair(e.parentEnv['vars'],new Pair(theNil,theNil))))));if(r!=theTC||r.f!=this)return r}})).With('_25_',new Lambda(new Pair(getSymbol('x'),theNil),new Pair(getSymbol('begin'),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('new'),new Pair(false,theNil))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eq?'),new Pair(getSymbol('x'),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('...'),theNil)),theNil))),new Pair(getSymbol('x'),new Pair(new Pair(getSymbol('begin'),new Pair(new Pair(getSymbol('set!'),new Pair(getSymbol('new'),new Pair(new Pair(getSymbol('gen-sym'),new Pair(getSymbol('x'),theNil)),theNil))),new Pair(new Pair(getSymbol('set!'),new Pair(getSymbol('vars'),new Pair(new Pair(getSymbol('cons'),new Pair(new Pair(getSymbol('cons'),new Pair(getSymbol('x'),new Pair(getSymbol('new'),theNil))),new Pair(getSymbol('vars'),theNil))),theNil))),new Pair(getSymbol('new'),theNil)))),theNil)))),theNil))),e,function(list){var r,e=new Env(this.env);while(true){e['x']=list.car;r=(e['new']=false,((isEq(e['x'],getSymbol('...')))!=false?e['x']:(e['new']=Apply(TopEnv.get('gen-sym'),new Pair(e['x'],theNil)),e.set('vars',new Pair(new Pair(e['x'],e['new']),e.parentEnv['vars'])),e['new'])));if(r!=theTC||r.f!=this)return r}})).With('_26_',new Lambda(new Pair(getSymbol('templ'),new Pair(getSymbol('no...'),theNil)),new Pair(getSymbol('begin'),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('old-vars'),new Pair(false,theNil))),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('args'),new Pair(false,theNil))),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('body'),new Pair(false,theNil))),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('new'),new Pair(false,theNil))),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('x'),new Pair(false,theNil))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('null?'),new Pair(getSymbol('templ'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(theNil,theNil)),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('pair?'),new Pair(getSymbol('templ'),theNil)),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('if'),new Pair(getSymbol('no...'),new Pair(new Pair(getSymbol('eq?'),new Pair(new Pair(getSymbol('cadr'),new Pair(getSymbol('templ'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('...'),theNil)),theNil))),new Pair(false,theNil)))),new Pair(new Pair(getSymbol('append'),new Pair(new Pair(getSymbol('gen-many'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('templ'),theNil)),theNil)),new Pair(new Pair(getSymbol('gen'),new Pair(new Pair(getSymbol('cddr'),new Pair(getSymbol('templ'),theNil)),new Pair(getSymbol('no...'),theNil))),theNil))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('if'),new Pair(getSymbol('no...'),new Pair(new Pair(getSymbol('eq?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('templ'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('lambda'),theNil)),theNil))),new Pair(false,theNil)))),new Pair(new Pair(getSymbol('begin'),new Pair(new Pair(getSymbol('set!'),new Pair(getSymbol('old-vars'),new Pair(getSymbol('vars'),theNil))),new Pair(new Pair(getSymbol('set!'),new Pair(getSymbol('args'),new Pair(new Pair(getSymbol('gen'),new Pair(new Pair(getSymbol('cadr'),new Pair(getSymbol('templ'),theNil)),new Pair(getSymbol('no...'),theNil))),theNil))),new Pair(new Pair(getSymbol('set!'),new Pair(getSymbol('body'),new Pair(new Pair(getSymbol('gen'),new Pair(new Pair(getSymbol('cddr'),new Pair(getSymbol('templ'),theNil)),new Pair(getSymbol('no...'),theNil))),theNil))),new Pair(new Pair(getSymbol('set!'),new Pair(getSymbol('vars'),new Pair(new Pair(getSymbol('quote'),new Pair(theNil,theNil)),theNil))),new Pair(new Pair(getSymbol('set!'),new Pair(getSymbol('new'),new Pair(new Pair(getSymbol('map+'),new Pair(getSymbol('ren'),new Pair(getSymbol('args'),theNil))),theNil))),new Pair(new Pair(getSymbol('set!'),new Pair(getSymbol('new'),new Pair(new Pair(getSymbol('cons'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('templ'),theNil)),new Pair(new Pair(getSymbol('cons'),new Pair(getSymbol('new'),new Pair(new Pair(getSymbol('gen'),new Pair(getSymbol('body'),new Pair(false,theNil))),theNil))),theNil))),theNil))),new Pair(new Pair(getSymbol('set!'),new Pair(getSymbol('vars'),new Pair(getSymbol('old-vars'),theNil))),new Pair(getSymbol('new'),theNil))))))))),new Pair(new Pair(getSymbol('cons'),new Pair(new Pair(getSymbol('gen'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('templ'),theNil)),new Pair(getSymbol('no...'),theNil))),new Pair(new Pair(getSymbol('gen'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('templ'),theNil)),new Pair(getSymbol('no...'),theNil))),theNil))),theNil)))),theNil)))),new Pair(new Pair(getSymbol('begin'),new Pair(new Pair(getSymbol('set!'),new Pair(getSymbol('x'),new Pair(new Pair(getSymbol('assq'),new Pair(getSymbol('templ'),new Pair(getSymbol('vars'),theNil))),theNil))),new Pair(new Pair(getSymbol('if'),new Pair(getSymbol('x'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('x'),theNil)),new Pair(getSymbol('templ'),theNil)))),theNil))),theNil)))),theNil)))),theNil))))))),e,function(list){var r,e=new Env(this.env);while(true){e['templ']=list.car;e['no...']=list.cdr.car;r=(e['old-vars']=false,e['args']=false,e['body']=false,e['new']=false,e['x']=false,(((e['templ']==theNil))!=false?theNil:((((e['templ'])instanceof Pair))!=false?((((e['no...'])!=false?isEq(e['templ'].cdr.car,getSymbol('...')):false))!=false?TC(TopEnv.get('append'),list=new Pair(Apply(e.parentEnv['gen-many'],new Pair(e['templ'].car,theNil)),new Pair(Apply(e.parentEnv['gen'],new Pair(e['templ'].cdr.cdr,new Pair(e['no...'],theNil))),theNil))):((((e['no...'])!=false?isEq(e['templ'].car,getSymbol('lambda')):false))!=false?(e['old-vars']=e.parentEnv['vars'],e['args']=Apply(e.parentEnv['gen'],new Pair(e['templ'].cdr.car,new Pair(e['no...'],theNil))),e['body']=Apply(e.parentEnv['gen'],new Pair(e['templ'].cdr.cdr,new Pair(e['no...'],theNil))),e.set('vars',theNil),e['new']=Apply(TopEnv.get('map+'),new Pair(e.parentEnv['ren'],new Pair(e['args'],theNil))),e['new']=new Pair(e['templ'].car,new Pair(e['new'],Apply(e.parentEnv['gen'],new Pair(e['body'],new Pair(false,theNil))))),e.set('vars',e['old-vars']),e['new']):new Pair(Apply(e.parentEnv['gen'],new Pair(e['templ'].car,new Pair(e['no...'],theNil))),Apply(e.parentEnv['gen'],new Pair(e['templ'].cdr,new Pair(e['no...'],theNil)))))):(e['x']=Apply(TopEnv.get('assq'),new Pair(e['templ'],new Pair(e.parentEnv['vars'],theNil))),((e['x'])!=false?e['x'].cdr:e['templ'])))));if(r!=theTC||r.f!=this)return r}})),function(list){var r,e=new Env(this.env);while(true){e['expr']=list.car;e['literals']=list.cdr.car;e['p1']=list.cdr.cdr.car;e['more']=list.cdr.cdr.cdr;r=(e['vars']=theNil,e['match']=e.parentEnv['_19_'].clone(e),e['match-many']=e.parentEnv['_20_'].clone(e),e['find-all']=e.parentEnv['_21_'].clone(e),e['p-each']=e.parentEnv['_22_'].clone(e),e['process-many']=e.parentEnv['_23_'].clone(e),e['gen-many']=e.parentEnv['_24_'].clone(e),e['ren']=e.parentEnv['_25_'].clone(e),e['gen']=e.parentEnv['_26_'].clone(e),((Apply(e['match'],new Pair(e['expr'].cdr,new Pair(e['p1'].car.cdr,theNil))))!=false?TC(e['gen'],list=new Pair(e['p1'].cdr.car,new Pair(true,theNil))):(((e['more']==theNil))!=false?TC(TopEnv.get('error'),list=new Pair(("no pattern matches "+e['expr'].car.name),theNil)):TC(TopEnv.get('syntax-rules'),list=new Pair(e['expr'],new Pair(e['literals'],e['more'].ListCopy()))))));if(r!=theTC||r.f!=this)return r}});
e['and']=new Syntax(e.get('syntax-rules'),new Pair(theNil,new Pair(new Pair(new Pair(getSymbol('_'),theNil),new Pair(true,theNil)),new Pair(new Pair(new Pair(getSymbol('_'),new Pair(getSymbol('test'),theNil)),new Pair(getSymbol('test'),theNil)),new Pair(new Pair(new Pair(getSymbol('_'),new Pair(getSymbol('test1'),new Pair(getSymbol('test2'),new Pair(getSymbol('...'),theNil)))),new Pair(new Pair(getSymbol('if'),new Pair(getSymbol('test1'),new Pair(new Pair(getSymbol('and'),new Pair(getSymbol('test2'),new Pair(getSymbol('...'),theNil))),new Pair(false,theNil)))),theNil)),theNil)))));
e['or']=new Syntax(e.get('syntax-rules'),new Pair(theNil,new Pair(new Pair(new Pair(getSymbol('_'),theNil),new Pair(false,theNil)),new Pair(new Pair(new Pair(getSymbol('_'),new Pair(getSymbol('test'),theNil)),new Pair(getSymbol('test'),theNil)),new Pair(new Pair(new Pair(getSymbol('_'),new Pair(getSymbol('test1'),new Pair(getSymbol('test2'),new Pair(getSymbol('...'),theNil)))),new Pair(new Pair(getSymbol('let'),new Pair(new Pair(new Pair(getSymbol('_tmp_'),new Pair(getSymbol('test1'),theNil)),theNil),new Pair(new Pair(getSymbol('if'),new Pair(getSymbol('_tmp_'),new Pair(getSymbol('_tmp_'),new Pair(new Pair(getSymbol('or'),new Pair(getSymbol('test2'),new Pair(getSymbol('...'),theNil))),theNil)))),theNil))),theNil)),theNil)))));
e['let']=new Syntax(e.get('syntax-rules'),new Pair(theNil,new Pair(new Pair(new Pair(getSymbol('_'),new Pair(new Pair(new Pair(getSymbol('name'),new Pair(getSymbol('val'),theNil)),new Pair(getSymbol('...'),theNil)),new Pair(getSymbol('body1'),new Pair(getSymbol('...'),theNil)))),new Pair(new Pair(new Pair(getSymbol('lambda'),new Pair(new Pair(getSymbol('name'),new Pair(getSymbol('...'),theNil)),new Pair(getSymbol('body1'),new Pair(getSymbol('...'),theNil)))),new Pair(getSymbol('val'),new Pair(getSymbol('...'),theNil))),theNil)),new Pair(new Pair(new Pair(getSymbol('_'),new Pair(getSymbol('tag'),new Pair(new Pair(new Pair(getSymbol('name'),new Pair(getSymbol('val'),theNil)),new Pair(getSymbol('...'),theNil)),new Pair(getSymbol('body1'),new Pair(getSymbol('...'),theNil))))),new Pair(new Pair(new Pair(getSymbol('letrec'),new Pair(new Pair(new Pair(getSymbol('tag'),new Pair(new Pair(getSymbol('lambda'),new Pair(new Pair(getSymbol('name'),new Pair(getSymbol('...'),theNil)),new Pair(getSymbol('body1'),new Pair(getSymbol('...'),theNil)))),theNil)),theNil),new Pair(getSymbol('tag'),theNil))),new Pair(getSymbol('val'),new Pair(getSymbol('...'),theNil))),theNil)),theNil))));
e['cond']=new Syntax(e.get('syntax-rules'),new Pair(new Pair(getSymbol('else'),new Pair(getSymbol('=>'),theNil)),new Pair(new Pair(new Pair(getSymbol('_'),new Pair(new Pair(getSymbol('else'),new Pair(getSymbol('result1'),new Pair(getSymbol('...'),theNil))),theNil)),new Pair(new Pair(getSymbol('begin'),new Pair(getSymbol('result1'),new Pair(getSymbol('...'),theNil))),theNil)),new Pair(new Pair(new Pair(getSymbol('_'),new Pair(new Pair(getSymbol('test'),new Pair(getSymbol('=>'),new Pair(getSymbol('result'),theNil))),theNil)),new Pair(new Pair(getSymbol('let'),new Pair(new Pair(new Pair(getSymbol('_tmp_'),new Pair(getSymbol('test'),theNil)),theNil),new Pair(new Pair(getSymbol('if'),new Pair(getSymbol('_tmp_'),new Pair(new Pair(getSymbol('result'),new Pair(getSymbol('_tmp_'),theNil)),theNil))),theNil))),theNil)),new Pair(new Pair(new Pair(getSymbol('_'),new Pair(new Pair(getSymbol('test'),new Pair(getSymbol('=>'),new Pair(getSymbol('result'),theNil))),new Pair(getSymbol('clause1'),new Pair(getSymbol('...'),theNil)))),new Pair(new Pair(getSymbol('let'),new Pair(new Pair(new Pair(getSymbol('_tmp_'),new Pair(getSymbol('test'),theNil)),theNil),new Pair(new Pair(getSymbol('if'),new Pair(getSymbol('_tmp_'),new Pair(new Pair(getSymbol('result'),new Pair(getSymbol('_tmp_'),theNil)),new Pair(new Pair(getSymbol('cond'),new Pair(getSymbol('clause1'),new Pair(getSymbol('...'),theNil))),theNil)))),theNil))),theNil)),new Pair(new Pair(new Pair(getSymbol('_'),new Pair(new Pair(getSymbol('test'),theNil),theNil)),new Pair(getSymbol('test'),theNil)),new Pair(new Pair(new Pair(getSymbol('_'),new Pair(new Pair(getSymbol('test'),theNil),new Pair(getSymbol('clause1'),new Pair(getSymbol('...'),theNil)))),new Pair(new Pair(getSymbol('let'),new Pair(new Pair(new Pair(getSymbol('_tmp_'),new Pair(getSymbol('test'),theNil)),theNil),new Pair(new Pair(getSymbol('if'),new Pair(getSymbol('_tmp_'),new Pair(getSymbol('_tmp_'),new Pair(new Pair(getSymbol('cond'),new Pair(getSymbol('clause1'),new Pair(getSymbol('...'),theNil))),theNil)))),theNil))),theNil)),new Pair(new Pair(new Pair(getSymbol('_'),new Pair(new Pair(getSymbol('test'),new Pair(getSymbol('result1'),new Pair(getSymbol('...'),theNil))),theNil)),new Pair(new Pair(getSymbol('if'),new Pair(getSymbol('test'),new Pair(new Pair(getSymbol('begin'),new Pair(getSymbol('result1'),new Pair(getSymbol('...'),theNil))),theNil))),theNil)),new Pair(new Pair(new Pair(getSymbol('_'),new Pair(new Pair(getSymbol('test'),new Pair(getSymbol('result1'),new Pair(getSymbol('...'),theNil))),new Pair(getSymbol('clause1'),new Pair(getSymbol('...'),theNil)))),new Pair(new Pair(getSymbol('if'),new Pair(getSymbol('test'),new Pair(new Pair(getSymbol('begin'),new Pair(getSymbol('result1'),new Pair(getSymbol('...'),theNil))),new Pair(new Pair(getSymbol('cond'),new Pair(getSymbol('clause1'),new Pair(getSymbol('...'),theNil))),theNil)))),theNil)),theNil)))))))));
e['let*']=new Syntax(e.get('syntax-rules'),new Pair(theNil,new Pair(new Pair(new Pair(getSymbol('_'),new Pair(theNil,new Pair(getSymbol('body1'),new Pair(getSymbol('...'),theNil)))),new Pair(new Pair(getSymbol('begin'),new Pair(getSymbol('body1'),new Pair(getSymbol('...'),theNil))),theNil)),new Pair(new Pair(new Pair(getSymbol('_'),new Pair(new Pair(new Pair(getSymbol('name1'),new Pair(getSymbol('val1'),theNil)),new Pair(new Pair(getSymbol('name2'),new Pair(getSymbol('val2'),theNil)),new Pair(getSymbol('...'),theNil))),new Pair(getSymbol('body1'),new Pair(getSymbol('...'),theNil)))),new Pair(new Pair(new Pair(getSymbol('lambda'),new Pair(new Pair(getSymbol('name1'),theNil),new Pair(new Pair(getSymbol('let*'),new Pair(new Pair(new Pair(getSymbol('name2'),new Pair(getSymbol('val2'),theNil)),new Pair(getSymbol('...'),theNil)),new Pair(getSymbol('body1'),new Pair(getSymbol('...'),theNil)))),theNil))),new Pair(getSymbol('val1'),theNil)),theNil)),theNil))));
e['letrec']=new Syntax(e.get('syntax-rules'),new Pair(theNil,new Pair(new Pair(new Pair(getSymbol('_'),new Pair(new Pair(new Pair(getSymbol('var1'),new Pair(getSymbol('init1'),theNil)),new Pair(getSymbol('...'),theNil)),new Pair(getSymbol('body'),new Pair(getSymbol('...'),theNil)))),new Pair(new Pair(new Pair(getSymbol('lambda'),new Pair(theNil,new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('var1'),new Pair(false,theNil))),new Pair(getSymbol('...'),new Pair(new Pair(new Pair(getSymbol('lambda'),new Pair(getSymbol('_tmplst_'),new Pair(new Pair(getSymbol('begin'),new Pair(new Pair(getSymbol('set!'),new Pair(getSymbol('var1'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('_tmplst_'),theNil)),theNil))),new Pair(new Pair(getSymbol('set!'),new Pair(getSymbol('_tmplst_'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('_tmplst_'),theNil)),theNil))),theNil))),new Pair(getSymbol('...'),theNil)))),new Pair(getSymbol('init1'),new Pair(getSymbol('...'),theNil))),new Pair(getSymbol('body'),new Pair(getSymbol('...'),theNil))))))),theNil),theNil)),theNil)));
e['let-syntax']=new Syntax(e.get('syntax-rules'),new Pair(theNil,new Pair(new Pair(new Pair(getSymbol('_'),new Pair(new Pair(new Pair(getSymbol('_var1_'),new Pair(getSymbol('_init1_'),theNil)),new Pair(getSymbol('...'),theNil)),new Pair(getSymbol('_body_'),new Pair(getSymbol('...'),theNil)))),new Pair(new Pair(new Pair(getSymbol('lambda'),new Pair(theNil,new Pair(new Pair(getSymbol('define-syntax'),new Pair(getSymbol('_var1_'),new Pair(getSymbol('_init1_'),theNil))),new Pair(getSymbol('...'),new Pair(getSymbol('_body_'),new Pair(getSymbol('...'),theNil)))))),theNil),theNil)),theNil)));
e['letrec-syntax']=e.get('let-syntax');
e['case']=new Syntax(e.get('syntax-rules'),new Pair(new Pair(getSymbol('else'),theNil),new Pair(new Pair(new Pair(getSymbol('_'),new Pair(new Pair(getSymbol('key'),new Pair(getSymbol('...'),theNil)),new Pair(getSymbol('clauses'),new Pair(getSymbol('...'),theNil)))),new Pair(new Pair(getSymbol('let'),new Pair(new Pair(new Pair(getSymbol('_tmp_'),new Pair(new Pair(getSymbol('key'),new Pair(getSymbol('...'),theNil)),theNil)),theNil),new Pair(new Pair(getSymbol('case'),new Pair(getSymbol('_tmp_'),new Pair(getSymbol('clauses'),new Pair(getSymbol('...'),theNil)))),theNil))),theNil)),new Pair(new Pair(new Pair(getSymbol('_'),new Pair(getSymbol('key'),new Pair(new Pair(getSymbol('else'),new Pair(getSymbol('result1'),new Pair(getSymbol('...'),theNil))),theNil))),new Pair(new Pair(getSymbol('begin'),new Pair(getSymbol('result1'),new Pair(getSymbol('...'),theNil))),theNil)),new Pair(new Pair(new Pair(getSymbol('_'),new Pair(getSymbol('key'),new Pair(new Pair(new Pair(getSymbol('atoms'),new Pair(getSymbol('...'),theNil)),new Pair(getSymbol('result1'),new Pair(getSymbol('...'),theNil))),theNil))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('memv'),new Pair(getSymbol('key'),new Pair(new Pair(getSymbol('quote'),new Pair(new Pair(getSymbol('atoms'),new Pair(getSymbol('...'),theNil)),theNil)),theNil))),new Pair(new Pair(getSymbol('begin'),new Pair(getSymbol('result1'),new Pair(getSymbol('...'),theNil))),theNil))),theNil)),new Pair(new Pair(new Pair(getSymbol('_'),new Pair(getSymbol('key'),new Pair(new Pair(new Pair(getSymbol('atoms'),new Pair(getSymbol('...'),theNil)),new Pair(getSymbol('result1'),new Pair(getSymbol('...'),theNil))),new Pair(getSymbol('clause'),new Pair(getSymbol('...'),theNil))))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('memv'),new Pair(getSymbol('key'),new Pair(new Pair(getSymbol('quote'),new Pair(new Pair(getSymbol('atoms'),new Pair(getSymbol('...'),theNil)),theNil)),theNil))),new Pair(new Pair(getSymbol('begin'),new Pair(getSymbol('result1'),new Pair(getSymbol('...'),theNil))),new Pair(new Pair(getSymbol('case'),new Pair(getSymbol('key'),new Pair(getSymbol('clause'),new Pair(getSymbol('...'),theNil)))),theNil)))),theNil)),theNil))))));
e['do']=new Syntax(e.get('syntax-rules'),new Pair(theNil,new Pair(new Pair(new Pair(getSymbol('_'),new Pair(new Pair(new Pair(getSymbol('var'),new Pair(getSymbol('init'),new Pair(getSymbol('step'),theNil))),new Pair(getSymbol('...'),theNil)),new Pair(new Pair(getSymbol('test'),new Pair(getSymbol('expr'),new Pair(getSymbol('...'),theNil))),new Pair(getSymbol('command'),new Pair(getSymbol('...'),theNil))))),new Pair(new Pair(getSymbol('letrec'),new Pair(new Pair(new Pair(getSymbol('_loop_'),new Pair(new Pair(getSymbol('lambda'),new Pair(new Pair(getSymbol('var'),new Pair(getSymbol('...'),theNil)),new Pair(new Pair(getSymbol('if'),new Pair(getSymbol('test'),new Pair(new Pair(getSymbol('begin'),new Pair(getSymbol('expr'),new Pair(getSymbol('...'),theNil))),new Pair(new Pair(getSymbol('begin'),new Pair(getSymbol('command'),new Pair(getSymbol('...'),new Pair(new Pair(getSymbol('_loop_'),new Pair(new Pair(getSymbol('do'),new Pair("step",new Pair(getSymbol('var'),new Pair(getSymbol('step'),theNil)))),new Pair(getSymbol('...'),theNil))),theNil)))),theNil)))),theNil))),theNil)),theNil),new Pair(new Pair(getSymbol('_loop_'),new Pair(getSymbol('init'),new Pair(getSymbol('...'),theNil))),theNil))),theNil)),new Pair(new Pair(new Pair(getSymbol('_'),new Pair("step",new Pair(getSymbol('x'),theNil))),new Pair(getSymbol('x'),theNil)),new Pair(new Pair(new Pair(getSymbol('_'),new Pair("step",new Pair(getSymbol('x'),new Pair(getSymbol('y'),theNil)))),new Pair(getSymbol('y'),theNil)),theNil)))));
e['memq+']=new Lambda(new Pair(getSymbol('x'),new Pair(getSymbol('ls'),theNil)),new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('pair?'),new Pair(getSymbol('ls'),theNil)),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eq?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ls'),theNil)),new Pair(getSymbol('x'),theNil))),new Pair(getSymbol('ls'),new Pair(new Pair(getSymbol('memq+'),new Pair(getSymbol('x'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('ls'),theNil)),theNil))),theNil)))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eq?'),new Pair(getSymbol('x'),new Pair(getSymbol('ls'),theNil))),new Pair(getSymbol('ls'),new Pair(false,theNil)))),theNil)))),e,function(list){var r,e=new Env(this.env);while(true){e['x']=list.car;e['ls']=list.cdr.car;r=((((e['ls'])instanceof Pair))!=false?((isEq(e['ls'].car,e['x']))!=false?e['ls']:TC(TopEnv.get('memq+'),list=new Pair(e['x'],new Pair(e['ls'].cdr,theNil)))):((isEq(e['x'],e['ls']))!=false?e['ls']:false));if(r!=theTC||r.f!=this)return r}});
e['memq']=e.get('memq+');
e['memv']=new Lambda(new Pair(getSymbol('x'),new Pair(getSymbol('ls'),theNil)),new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('pair?'),new Pair(getSymbol('ls'),theNil)),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eqv?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ls'),theNil)),new Pair(getSymbol('x'),theNil))),new Pair(getSymbol('ls'),new Pair(new Pair(getSymbol('memv'),new Pair(getSymbol('x'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('ls'),theNil)),theNil))),theNil)))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eqv?'),new Pair(getSymbol('x'),new Pair(getSymbol('ls'),theNil))),new Pair(getSymbol('ls'),new Pair(false,theNil)))),theNil)))),e,function(list){var r,e=new Env(this.env);while(true){e['x']=list.car;e['ls']=list.cdr.car;r=((((e['ls'])instanceof Pair))!=false?((isEq(e['ls'].car,e['x']))!=false?e['ls']:TC(TopEnv.get('memv'),list=new Pair(e['x'],new Pair(e['ls'].cdr,theNil)))):((isEq(e['x'],e['ls']))!=false?e['ls']:false));if(r!=theTC||r.f!=this)return r}});
e['member']=new Lambda(new Pair(getSymbol('x'),new Pair(getSymbol('ls'),theNil)),new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('pair?'),new Pair(getSymbol('ls'),theNil)),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('equal?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ls'),theNil)),new Pair(getSymbol('x'),theNil))),new Pair(getSymbol('ls'),new Pair(new Pair(getSymbol('member'),new Pair(getSymbol('x'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('ls'),theNil)),theNil))),theNil)))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('equal?'),new Pair(getSymbol('x'),new Pair(getSymbol('ls'),theNil))),new Pair(getSymbol('ls'),new Pair(false,theNil)))),theNil)))),e,function(list){var r,e=new Env(this.env);while(true){e['x']=list.car;e['ls']=list.cdr.car;r=((((e['ls'])instanceof Pair))!=false?((Apply(TopEnv.get('equal?'),new Pair(e['ls'].car,new Pair(e['x'],theNil))))!=false?e['ls']:TC(TopEnv.get('member'),list=new Pair(e['x'],new Pair(e['ls'].cdr,theNil)))):((Apply(TopEnv.get('equal?'),new Pair(e['x'],new Pair(e['ls'],theNil))))!=false?e['ls']:false));if(r!=theTC||r.f!=this)return r}});
e['assq']=new Lambda(new Pair(getSymbol('x'),new Pair(getSymbol('ls'),theNil)),new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('null?'),new Pair(getSymbol('ls'),theNil)),new Pair(false,new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eq?'),new Pair(new Pair(getSymbol('caar'),new Pair(getSymbol('ls'),theNil)),new Pair(getSymbol('x'),theNil))),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ls'),theNil)),new Pair(new Pair(getSymbol('assq'),new Pair(getSymbol('x'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('ls'),theNil)),theNil))),theNil)))),theNil)))),e,function(list){var r,e=new Env(this.env);while(true){e['x']=list.car;e['ls']=list.cdr.car;r=(((e['ls']==theNil))!=false?false:((isEq(e['ls'].car.car,e['x']))!=false?e['ls'].car:TC(TopEnv.get('assq'),list=new Pair(e['x'],new Pair(e['ls'].cdr,theNil)))));if(r!=theTC||r.f!=this)return r}});
e['assv']=new Lambda(new Pair(getSymbol('x'),new Pair(getSymbol('ls'),theNil)),new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('null?'),new Pair(getSymbol('ls'),theNil)),new Pair(false,new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eqv?'),new Pair(new Pair(getSymbol('caar'),new Pair(getSymbol('ls'),theNil)),new Pair(getSymbol('x'),theNil))),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ls'),theNil)),new Pair(new Pair(getSymbol('assv'),new Pair(getSymbol('x'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('ls'),theNil)),theNil))),theNil)))),theNil)))),e,function(list){var r,e=new Env(this.env);while(true){e['x']=list.car;e['ls']=list.cdr.car;r=(((e['ls']==theNil))!=false?false:((isEq(e['ls'].car.car,e['x']))!=false?e['ls'].car:TC(TopEnv.get('assv'),list=new Pair(e['x'],new Pair(e['ls'].cdr,theNil)))));if(r!=theTC||r.f!=this)return r}});
e['assoc']=new Lambda(new Pair(getSymbol('x'),new Pair(getSymbol('ls'),theNil)),new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('null?'),new Pair(getSymbol('ls'),theNil)),new Pair(false,new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('equal?'),new Pair(new Pair(getSymbol('caar'),new Pair(getSymbol('ls'),theNil)),new Pair(getSymbol('x'),theNil))),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ls'),theNil)),new Pair(new Pair(getSymbol('assoc'),new Pair(getSymbol('x'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('ls'),theNil)),theNil))),theNil)))),theNil)))),e,function(list){var r,e=new Env(this.env);while(true){e['x']=list.car;e['ls']=list.cdr.car;r=(((e['ls']==theNil))!=false?false:((Apply(TopEnv.get('equal?'),new Pair(e['ls'].car.car,new Pair(e['x'],theNil))))!=false?e['ls'].car:TC(TopEnv.get('assoc'),list=new Pair(e['x'],new Pair(e['ls'].cdr,theNil)))));if(r!=theTC||r.f!=this)return r}});
e['list?']=Apply(new Lambda(theNil,new Pair(getSymbol('begin'),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('race'),new Pair(new Pair(getSymbol('clone'),new Pair(getSymbol('_28_'),theNil)),theNil))),new Pair(new Pair(getSymbol('clone'),new Pair(getSymbol('_29_'),theNil)),theNil))),new Env(e).With('_28_',new Lambda(new Pair(getSymbol('h'),new Pair(getSymbol('t'),theNil)),new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('pair?'),new Pair(getSymbol('h'),theNil)),new Pair(new Pair(new Pair(getSymbol('clone'),new Pair(getSymbol('_30_'),theNil)),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('h'),theNil)),theNil)),new Pair(new Pair(getSymbol('null?'),new Pair(getSymbol('h'),theNil)),theNil)))),new Env(e).With('_30_',new Lambda(new Pair(getSymbol('h'),theNil),new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('pair?'),new Pair(getSymbol('h'),theNil)),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('not'),new Pair(new Pair(getSymbol('eq?'),new Pair(getSymbol('h'),new Pair(getSymbol('t'),theNil))),theNil)),new Pair(new Pair(getSymbol('race'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('h'),theNil)),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('t'),theNil)),theNil))),new Pair(false,theNil)))),new Pair(new Pair(getSymbol('null?'),new Pair(getSymbol('h'),theNil)),theNil)))),e,function(list){var r,e=new Env(this.env);while(true){e['h']=list.car;r=((((e['h'])instanceof Pair))!=false?(((isEq(e['h'],e.parentEnv['t'])==false))!=false?TC(e.parentEnv.parentEnv.parentEnv['race'],list=new Pair(e['h'].cdr,new Pair(e.parentEnv['t'].cdr,theNil))):false):(e['h']==theNil));if(r!=theTC||r.f!=this)return r}})),function(list){var r,e=new Env(this.env);while(true){e['h']=list.car;e['t']=list.cdr.car;r=((((e['h'])instanceof Pair))!=false?TC(e.parentEnv['_30_'].clone(e),list=new Pair(e['h'].cdr,theNil)):(e['h']==theNil));if(r!=theTC||r.f!=this)return r}})).With('_29_',new Lambda(new Pair(getSymbol('x'),theNil),new Pair(getSymbol('race'),new Pair(getSymbol('x'),new Pair(getSymbol('x'),theNil))),e,function(list){var r,e=new Env(this.env);while(true){e['x']=list.car;r=TC(e.parentEnv['race'],list=new Pair(e['x'],new Pair(e['x'],theNil)));if(r!=theTC||r.f!=this)return r}})),function(list){var r,e=new Env(this.env);while(true){r=(e['race']=e.parentEnv['_28_'].clone(e),e.parentEnv['_29_'].clone(e));if(r!=theTC||r.f!=this)return r}}),theNil);
e['equal?']=new Lambda(new Pair(getSymbol('x'),new Pair(getSymbol('y'),theNil)),new Pair(new Pair(getSymbol('clone'),new Pair(getSymbol('_31_'),theNil)),new Pair(new Pair(getSymbol('eqv?'),new Pair(getSymbol('x'),new Pair(getSymbol('y'),theNil))),theNil)),new Env(e).With('_31_',new Lambda(new Pair(getSymbol('eqv'),theNil),new Pair(getSymbol('if'),new Pair(getSymbol('eqv'),new Pair(getSymbol('eqv'),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('pair?'),new Pair(getSymbol('x'),theNil)),new Pair(new Pair(getSymbol('begin'),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('pair?'),new Pair(getSymbol('y'),theNil)),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('equal?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('x'),theNil)),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('y'),theNil)),theNil))),new Pair(new Pair(getSymbol('equal?'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('x'),theNil)),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('y'),theNil)),theNil))),new Pair(false,theNil)))),new Pair(false,theNil)))),theNil)),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('vector?'),new Pair(getSymbol('x'),theNil)),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('vector?'),new Pair(getSymbol('y'),theNil)),new Pair(new Pair(new Pair(getSymbol('clone'),new Pair(getSymbol('_32_'),theNil)),new Pair(new Pair(getSymbol('vector-length'),new Pair(getSymbol('x'),theNil)),theNil)),new Pair(false,theNil)))),new Pair(false,theNil)))),theNil)))),theNil)))),new Env(e).With('_32_',new Lambda(new Pair(getSymbol('n'),theNil),new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('='),new Pair(new Pair(getSymbol('vector-length'),new Pair(getSymbol('y'),theNil)),new Pair(getSymbol('n'),theNil))),new Pair(new Pair(new Pair(getSymbol('begin'),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('loop'),new Pair(new Pair(getSymbol('clone'),new Pair(getSymbol('_33_'),theNil)),theNil))),new Pair(getSymbol('loop'),theNil))),new Pair(0,theNil)),new Pair(false,theNil)))),new Env(e).With('_33_',new Lambda(new Pair(getSymbol('i'),theNil),new Pair(new Pair(getSymbol('clone'),new Pair(getSymbol('_34_'),theNil)),new Pair(new Pair(getSymbol('='),new Pair(getSymbol('i'),new Pair(getSymbol('n'),theNil))),theNil)),new Env(e).With('_34_',new Lambda(new Pair(getSymbol('eq-len'),theNil),new Pair(getSymbol('if'),new Pair(getSymbol('eq-len'),new Pair(getSymbol('eq-len'),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('equal?'),new Pair(new Pair(getSymbol('vector-ref'),new Pair(getSymbol('x'),new Pair(getSymbol('i'),theNil))),new Pair(new Pair(getSymbol('vector-ref'),new Pair(getSymbol('y'),new Pair(getSymbol('i'),theNil))),theNil))),new Pair(new Pair(getSymbol('loop'),new Pair(new Pair(getSymbol('+'),new Pair(getSymbol('i'),new Pair(1,theNil))),theNil)),new Pair(false,theNil)))),theNil)))),e,function(list){var r,e=new Env(this.env);while(true){e['eq-len']=list.car;r=((e['eq-len'])!=false?e['eq-len']:((Apply(TopEnv.get('equal?'),new Pair(Apply(TopEnv.get('vector-ref'),new Pair(e.parentEnv.parentEnv.parentEnv.parentEnv.parentEnv.parentEnv.parentEnv['x'],new Pair(e.parentEnv['i'],theNil))),new Pair(Apply(TopEnv.get('vector-ref'),new Pair(e.parentEnv.parentEnv.parentEnv.parentEnv.parentEnv.parentEnv.parentEnv['y'],new Pair(e.parentEnv['i'],theNil))),theNil))))!=false?TC(e.parentEnv.parentEnv.parentEnv['loop'],list=new Pair((e.parentEnv['i']+1),theNil)):false));if(r!=theTC||r.f!=this)return r}})),function(list){var r,e=new Env(this.env);while(true){e['i']=list.car;r=TC(e.parentEnv['_34_'].clone(e),list=new Pair(isEq(e['i'],e.parentEnv.parentEnv['n']),theNil));if(r!=theTC||r.f!=this)return r}})),function(list){var r,e=new Env(this.env);while(true){e['n']=list.car;r=((isEq(Apply(TopEnv.get('vector-length'),new Pair(e.parentEnv.parentEnv.parentEnv.parentEnv['y'],theNil)),e['n']))!=false?TC((e['loop']=e.parentEnv['_33_'].clone(e),e['loop']),list=new Pair(0,theNil)):false);if(r!=theTC||r.f!=this)return r}})),function(list){var r,e=new Env(this.env);while(true){e['eqv']=list.car;r=((e['eqv'])!=false?e['eqv']:((((e.parentEnv.parentEnv['x'])instanceof Pair))!=false?((((e.parentEnv.parentEnv['y'])instanceof Pair))!=false?((Apply(TopEnv.get('equal?'),new Pair(e.parentEnv.parentEnv['x'].car,new Pair(e.parentEnv.parentEnv['y'].car,theNil))))!=false?TC(TopEnv.get('equal?'),list=new Pair(e.parentEnv.parentEnv['x'].cdr,new Pair(e.parentEnv.parentEnv['y'].cdr,theNil))):false):false):((Apply(TopEnv.get('vector?'),new Pair(e.parentEnv.parentEnv['x'],theNil)))!=false?((Apply(TopEnv.get('vector?'),new Pair(e.parentEnv.parentEnv['y'],theNil)))!=false?TC(e.parentEnv['_32_'].clone(e),list=new Pair(Apply(TopEnv.get('vector-length'),new Pair(e.parentEnv.parentEnv['x'],theNil)),theNil)):false):false)));if(r!=theTC||r.f!=this)return r}})),function(list){var r,e=new Env(this.env);while(true){e['x']=list.car;e['y']=list.cdr.car;r=TC(e.parentEnv['_31_'].clone(e),list=new Pair(isEq(e['x'],e['y']),theNil));if(r!=theTC||r.f!=this)return r}});
e['values']=new Lambda(getSymbol('things'),new Pair(getSymbol('call/cc'),new Pair(new Pair(getSymbol('clone'),new Pair(getSymbol('_35_'),theNil)),theNil)),new Env(e).With('_35_',new Lambda(new Pair(getSymbol('cont'),theNil),new Pair(getSymbol('apply'),new Pair(getSymbol('cont'),new Pair(getSymbol('things'),theNil))),e,function(list){var r,e=new Env(this.env);while(true){e['cont']=list.car;r=TC(e['cont'],list=e.parentEnv['things'].ListCopy());if(r!=theTC||r.f!=this)return r}})),function(list){var r,e=new Env(this.env);while(true){e['things']=list;r=TC(TopEnv.get('call/cc'),list=new Pair(e.parentEnv['_35_'].clone(e),theNil));if(r!=theTC||r.f!=this)return r}});
e['call-with-values']=new Lambda(new Pair(getSymbol('producer'),new Pair(getSymbol('consumer'),theNil)),new Pair(getSymbol('consumer'),new Pair(new Pair(getSymbol('producer'),theNil),theNil)),e,function(list){var r,e=new Env(this.env);while(true){e['producer']=list.car;e['consumer']=list.cdr.car;r=TC(e['consumer'],list=new Pair(Apply(e['producer'],theNil),theNil));if(r!=theTC||r.f!=this)return r}});
e['for-each']=new Lambda(new Pair(getSymbol('f'),getSymbol('lst')),new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('not'),new Pair(new Pair(getSymbol('null?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('lst'),theNil)),theNil)),theNil)),new Pair(new Pair(getSymbol('begin'),new Pair(new Pair(getSymbol('apply'),new Pair(getSymbol('f'),new Pair(new Pair(getSymbol('map+'),new Pair(getSymbol('car'),new Pair(getSymbol('lst'),theNil))),theNil))),new Pair(new Pair(getSymbol('apply'),new Pair(getSymbol('for-each'),new Pair(getSymbol('f'),new Pair(new Pair(getSymbol('map+'),new Pair(getSymbol('cdr'),new Pair(getSymbol('lst'),theNil))),theNil)))),theNil))),theNil))),e,function(list){var r,e=new Env(this.env);while(true){e['f']=list.car;e['lst']=list.cdr;r=((((e['lst'].car==theNil)==false))!=false?(Apply(e['f'],Apply(TopEnv.get('map+'),new Pair(TopEnv.get('car'),new Pair(e['lst'],theNil))).ListCopy()),TC(TopEnv.get('for-each'),list=new Pair(e['f'],Apply(TopEnv.get('map+'),new Pair(TopEnv.get('cdr'),new Pair(e['lst'],theNil))).ListCopy()))):null);if(r!=theTC||r.f!=this)return r}});
e['delay']=new Syntax(e.get('syntax-rules'),new Pair(theNil,new Pair(new Pair(new Pair(getSymbol('_'),new Pair(getSymbol('exp'),theNil)),new Pair(new Pair(getSymbol('make-promise'),new Pair(new Pair(getSymbol('lambda'),new Pair(theNil,new Pair(getSymbol('exp'),theNil))),theNil)),theNil)),theNil)));
e['make-promise']=new Lambda(new Pair(getSymbol('p'),theNil),new Pair(new Pair(getSymbol('clone'),new Pair(getSymbol('_36_'),theNil)),theNil),new Env(e).With('_36_',new Lambda(theNil,new Pair(getSymbol('begin'),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('val'),new Pair(false,theNil))),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('set?'),new Pair(false,theNil))),new Pair(new Pair(getSymbol('clone'),new Pair(getSymbol('_37_'),theNil)),theNil)))),new Env(e).With('_37_',new Lambda(theNil,new Pair(getSymbol('begin'),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('not'),new Pair(getSymbol('set?'),theNil)),new Pair(new Pair(getSymbol('begin'),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('x'),new Pair(new Pair(getSymbol('p'),theNil),theNil))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('not'),new Pair(getSymbol('set?'),theNil)),new Pair(new Pair(getSymbol('begin'),new Pair(new Pair(getSymbol('set!'),new Pair(getSymbol('val'),new Pair(getSymbol('x'),theNil))),new Pair(new Pair(getSymbol('set!'),new Pair(getSymbol('set?'),new Pair(true,theNil))),theNil))),theNil))),theNil))),theNil))),new Pair(getSymbol('val'),theNil))),e,function(list){var r,e=new Env(this.env);while(true){r=((((e.parentEnv['set?']==false))!=false?(e['x']=Apply(e.parentEnv.parentEnv.parentEnv['p'],theNil),(((e.parentEnv['set?']==false))!=false?(e.set('val',e['x']),e.set('set?',true)):null)):null),e.parentEnv['val']);if(r!=theTC||r.f!=this)return r}})),function(list){var r,e=new Env(this.env);while(true){r=(e['val']=false,e['set?']=false,e.parentEnv['_37_'].clone(e));if(r!=theTC||r.f!=this)return r}})),function(list){var r,e=new Env(this.env);while(true){e['p']=list.car;r=TC(e.parentEnv['_36_'].clone(e),list=theNil);if(r!=theTC||r.f!=this)return r}});
e['force']=new Lambda(new Pair(getSymbol('promise'),theNil),new Pair(getSymbol('promise'),theNil),e,function(list){var r,e=new Env(this.env);while(true){e['promise']=list.car;r=TC(e['promise'],list=theNil);if(r!=theTC||r.f!=this)return r}});
e['string-copy']=new Lambda(new Pair(getSymbol('x'),theNil),getSymbol('x'),e,function(list){var r,e=new Env(this.env);while(true){e['x']=list.car;r=e['x'];if(r!=theTC||r.f!=this)return r}});
e['vector-fill!']=new Lambda(new Pair(getSymbol('v'),new Pair(getSymbol('obj'),theNil)),new Pair(getSymbol('begin'),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('l'),new Pair(new Pair(getSymbol('vector-length'),new Pair(getSymbol('v'),theNil)),theNil))),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('vf'),new Pair(new Pair(getSymbol('clone'),new Pair(getSymbol('_38_'),theNil)),theNil))),new Pair(new Pair(getSymbol('vf'),new Pair(0,theNil)),theNil)))),new Env(e).With('_38_',new Lambda(new Pair(getSymbol('i'),theNil),new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('<'),new Pair(getSymbol('i'),new Pair(getSymbol('l'),theNil))),new Pair(new Pair(getSymbol('begin'),new Pair(new Pair(getSymbol('vector-set!'),new Pair(getSymbol('v'),new Pair(getSymbol('i'),new Pair(getSymbol('obj'),theNil)))),new Pair(new Pair(getSymbol('vf'),new Pair(new Pair(getSymbol('+'),new Pair(getSymbol('i'),new Pair(1,theNil))),theNil)),theNil))),theNil))),e,function(list){var r,e=new Env(this.env);while(true){e['i']=list.car;r=((e['i']<e.parentEnv['l'])!=false?(Apply(TopEnv.get('vector-set!'),new Pair(e.parentEnv['v'],new Pair(e['i'],new Pair(e.parentEnv['obj'],theNil)))),TC(e.parentEnv['vf'],list=new Pair((e['i']+1),theNil))):null);if(r!=theTC||r.f!=this)return r}})),function(list){var r,e=new Env(this.env);while(true){e['v']=list.car;e['obj']=list.cdr.car;r=(e['l']=Apply(TopEnv.get('vector-length'),new Pair(e['v'],theNil)),e['vf']=e.parentEnv['_38_'].clone(e),TC(e['vf'],list=new Pair(0,theNil)));if(r!=theTC||r.f!=this)return r}});
e['vector->list']=new Lambda(new Pair(getSymbol('v'),theNil),new Pair(getSymbol('begin'),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('loop'),new Pair(new Pair(getSymbol('clone'),new Pair(getSymbol('_39_'),theNil)),theNil))),new Pair(new Pair(getSymbol('loop'),new Pair(new Pair(getSymbol('-'),new Pair(new Pair(getSymbol('vector-length'),new Pair(getSymbol('v'),theNil)),new Pair(1,theNil))),new Pair(new Pair(getSymbol('quote'),new Pair(theNil,theNil)),theNil))),theNil))),new Env(e).With('_39_',new Lambda(new Pair(getSymbol('i'),new Pair(getSymbol('l'),theNil)),new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('<'),new Pair(getSymbol('i'),new Pair(0,theNil))),new Pair(getSymbol('l'),new Pair(new Pair(getSymbol('loop'),new Pair(new Pair(getSymbol('-'),new Pair(getSymbol('i'),new Pair(1,theNil))),new Pair(new Pair(getSymbol('cons'),new Pair(new Pair(getSymbol('vector-ref'),new Pair(getSymbol('v'),new Pair(getSymbol('i'),theNil))),new Pair(getSymbol('l'),theNil))),theNil))),theNil)))),e,function(list){var r,e=new Env(this.env);while(true){e['i']=list.car;e['l']=list.cdr.car;r=((e['i']<0)!=false?e['l']:TC(e.parentEnv['loop'],list=new Pair((e['i']-1),new Pair(new Pair(Apply(TopEnv.get('vector-ref'),new Pair(e.parentEnv['v'],new Pair(e['i'],theNil))),e['l']),theNil))));if(r!=theTC||r.f!=this)return r}})),function(list){var r,e=new Env(this.env);while(true){e['v']=list.car;r=(e['loop']=e.parentEnv['_39_'].clone(e),TC(e['loop'],list=new Pair((Apply(TopEnv.get('vector-length'),new Pair(e['v'],theNil))-1),new Pair(theNil,theNil))));if(r!=theTC||r.f!=this)return r}});
e['list->vector']=new Lambda(new Pair(getSymbol('l'),theNil),new Pair(getSymbol('begin'),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('v'),new Pair(new Pair(getSymbol('make-vector'),new Pair(0,theNil)),theNil))),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('loop'),new Pair(new Pair(getSymbol('clone'),new Pair(getSymbol('_40_'),theNil)),theNil))),new Pair(new Pair(getSymbol('loop'),new Pair(0,new Pair(getSymbol('l'),theNil))),new Pair(getSymbol('v'),theNil))))),new Env(e).With('_40_',new Lambda(new Pair(getSymbol('i'),new Pair(getSymbol('l'),theNil)),new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('pair?'),new Pair(getSymbol('l'),theNil)),new Pair(new Pair(getSymbol('begin'),new Pair(new Pair(getSymbol('vector-set!'),new Pair(getSymbol('v'),new Pair(getSymbol('i'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('l'),theNil)),theNil)))),new Pair(new Pair(getSymbol('loop'),new Pair(new Pair(getSymbol('+'),new Pair(getSymbol('i'),new Pair(1,theNil))),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('l'),theNil)),theNil))),theNil))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('not'),new Pair(new Pair(getSymbol('null?'),new Pair(getSymbol('l'),theNil)),theNil)),new Pair(new Pair(getSymbol('vector-set!'),new Pair(getSymbol('v'),new Pair(getSymbol('i'),new Pair(getSymbol('l'),theNil)))),theNil))),theNil)))),e,function(list){var r,e=new Env(this.env);while(true){e['i']=list.car;e['l']=list.cdr.car;r=((((e['l'])instanceof Pair))!=false?(Apply(TopEnv.get('vector-set!'),new Pair(e.parentEnv['v'],new Pair(e['i'],new Pair(e['l'].car,theNil)))),TC(e.parentEnv['loop'],list=new Pair((e['i']+1),new Pair(e['l'].cdr,theNil)))):((((e['l']==theNil)==false))!=false?TC(TopEnv.get('vector-set!'),list=new Pair(e.parentEnv['v'],new Pair(e['i'],new Pair(e['l'],theNil)))):null));if(r!=theTC||r.f!=this)return r}})),function(list){var r,e=new Env(this.env);while(true){e['l']=list.car;r=(e['v']=Apply(TopEnv.get('make-vector'),new Pair(0,theNil)),e['loop']=e.parentEnv['_40_'].clone(e),Apply(e['loop'],new Pair(0,new Pair(e['l'],theNil))),e['v']);if(r!=theTC||r.f!=this)return r}});
e['dynamic-wind']=false;
Apply(new Lambda(theNil,new Pair(getSymbol('begin'),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('winders'),new Pair(new Pair(getSymbol('quote'),new Pair(theNil,theNil)),theNil))),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('common-tail'),new Pair(new Pair(getSymbol('clone'),new Pair(getSymbol('_41_'),theNil)),theNil))),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('do-wind'),new Pair(new Pair(getSymbol('clone'),new Pair(getSymbol('_42_'),theNil)),theNil))),new Pair(new Pair(new Pair(getSymbol('clone'),new Pair(getSymbol('_43_'),theNil)),new Pair(getSymbol('call/cc'),theNil)),new Pair(new Pair(getSymbol('set!'),new Pair(getSymbol('call-with-current-continuation'),new Pair(getSymbol('call/cc'),theNil))),new Pair(new Pair(getSymbol('set!'),new Pair(getSymbol('dynamic-wind'),new Pair(new Pair(getSymbol('clone'),new Pair(getSymbol('_44_'),theNil)),theNil))),theNil))))))),new Env(e).With('_41_',new Lambda(new Pair(getSymbol('x'),new Pair(getSymbol('y'),theNil)),new Pair(getSymbol('begin'),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('lx'),new Pair(new Pair(getSymbol('length'),new Pair(getSymbol('x'),theNil)),theNil))),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('ly'),new Pair(new Pair(getSymbol('length'),new Pair(getSymbol('y'),theNil)),theNil))),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('loop'),new Pair(new Pair(getSymbol('clone'),new Pair(getSymbol('_45_'),theNil)),theNil))),new Pair(new Pair(getSymbol('loop'),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('>'),new Pair(getSymbol('lx'),new Pair(getSymbol('ly'),theNil))),new Pair(new Pair(getSymbol('list-tail'),new Pair(getSymbol('x'),new Pair(new Pair(getSymbol('-'),new Pair(getSymbol('lx'),new Pair(getSymbol('ly'),theNil))),theNil))),new Pair(getSymbol('x'),theNil)))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('>'),new Pair(getSymbol('ly'),new Pair(getSymbol('lx'),theNil))),new Pair(new Pair(getSymbol('list-tail'),new Pair(getSymbol('y'),new Pair(new Pair(getSymbol('-'),new Pair(getSymbol('ly'),new Pair(getSymbol('lx'),theNil))),theNil))),new Pair(getSymbol('y'),theNil)))),theNil))),theNil))))),new Env(e).With('_45_',new Lambda(new Pair(getSymbol('x'),new Pair(getSymbol('y'),theNil)),new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eq?'),new Pair(getSymbol('x'),new Pair(getSymbol('y'),theNil))),new Pair(getSymbol('x'),new Pair(new Pair(getSymbol('loop'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('x'),theNil)),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('y'),theNil)),theNil))),theNil)))),e,function(list){var r,e=new Env(this.env);while(true){e['x']=list.car;e['y']=list.cdr.car;r=((isEq(e['x'],e['y']))!=false?e['x']:TC(e.parentEnv['loop'],list=new Pair(e['x'].cdr,new Pair(e['y'].cdr,theNil))));if(r!=theTC||r.f!=this)return r}})),function(list){var r,e=new Env(this.env);while(true){e['x']=list.car;e['y']=list.cdr.car;r=(e['lx']=Apply(TopEnv.get('length'),new Pair(e['x'],theNil)),e['ly']=Apply(TopEnv.get('length'),new Pair(e['y'],theNil)),e['loop']=e.parentEnv['_45_'].clone(e),TC(e['loop'],list=new Pair(((e['lx']>e['ly'])!=false?Apply(TopEnv.get('list-tail'),new Pair(e['x'],new Pair((e['lx']-e['ly']),theNil))):e['x']),new Pair(((e['ly']>e['lx'])!=false?Apply(TopEnv.get('list-tail'),new Pair(e['y'],new Pair((e['ly']-e['lx']),theNil))):e['y']),theNil))));if(r!=theTC||r.f!=this)return r}})).With('_42_',new Lambda(new Pair(getSymbol('new'),theNil),new Pair(getSymbol('begin'),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('tail'),new Pair(new Pair(getSymbol('common-tail'),new Pair(getSymbol('new'),new Pair(getSymbol('winders'),theNil))),theNil))),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('f1'),new Pair(new Pair(getSymbol('clone'),new Pair(getSymbol('_46_'),theNil)),theNil))),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('f2'),new Pair(new Pair(getSymbol('clone'),new Pair(getSymbol('_47_'),theNil)),theNil))),new Pair(new Pair(getSymbol('f1'),new Pair(getSymbol('winders'),theNil)),new Pair(new Pair(getSymbol('f2'),new Pair(getSymbol('new'),theNil)),theNil)))))),new Env(e).With('_46_',new Lambda(new Pair(getSymbol('l'),theNil),new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('not'),new Pair(new Pair(getSymbol('eq?'),new Pair(getSymbol('l'),new Pair(getSymbol('tail'),theNil))),theNil)),new Pair(new Pair(getSymbol('begin'),new Pair(new Pair(getSymbol('set!'),new Pair(getSymbol('winders'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('l'),theNil)),theNil))),new Pair(new Pair(new Pair(getSymbol('cdar'),new Pair(getSymbol('l'),theNil)),theNil),new Pair(new Pair(getSymbol('f1'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('l'),theNil)),theNil)),theNil)))),theNil))),e,function(list){var r,e=new Env(this.env);while(true){e['l']=list.car;r=(((isEq(e['l'],e.parentEnv['tail'])==false))!=false?(e.set('winders',e['l'].cdr),Apply(e['l'].car.cdr,theNil),TC(e.parentEnv['f1'],list=new Pair(e['l'].cdr,theNil))):null);if(r!=theTC||r.f!=this)return r}})).With('_47_',new Lambda(new Pair(getSymbol('l'),theNil),new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('not'),new Pair(new Pair(getSymbol('eq?'),new Pair(getSymbol('l'),new Pair(getSymbol('tail'),theNil))),theNil)),new Pair(new Pair(getSymbol('begin'),new Pair(new Pair(getSymbol('f2'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('l'),theNil)),theNil)),new Pair(new Pair(new Pair(getSymbol('caar'),new Pair(getSymbol('l'),theNil)),theNil),new Pair(new Pair(getSymbol('set!'),new Pair(getSymbol('winders'),new Pair(getSymbol('l'),theNil))),theNil)))),theNil))),e,function(list){var r,e=new Env(this.env);while(true){e['l']=list.car;r=(((isEq(e['l'],e.parentEnv['tail'])==false))!=false?(Apply(e.parentEnv['f2'],new Pair(e['l'].cdr,theNil)),Apply(e['l'].car.car,theNil),e.set('winders',e['l'])):null);if(r!=theTC||r.f!=this)return r}})),function(list){var r,e=new Env(this.env);while(true){e['new']=list.car;r=(e['tail']=Apply(e.parentEnv.parentEnv['common-tail'],new Pair(e['new'],new Pair(e.parentEnv.parentEnv['winders'],theNil))),e['f1']=e.parentEnv['_46_'].clone(e),e['f2']=e.parentEnv['_47_'].clone(e),Apply(e['f1'],new Pair(e.parentEnv.parentEnv['winders'],theNil)),TC(e['f2'],list=new Pair(e['new'],theNil)));if(r!=theTC||r.f!=this)return r}})).With('_43_',new Lambda(new Pair(getSymbol('c'),theNil),new Pair(getSymbol('set!'),new Pair(getSymbol('call/cc'),new Pair(new Pair(getSymbol('clone'),new Pair(getSymbol('_48_'),theNil)),theNil))),new Env(e).With('_48_',new Lambda(new Pair(getSymbol('f'),theNil),new Pair(getSymbol('c'),new Pair(new Pair(getSymbol('clone'),new Pair(getSymbol('_49_'),theNil)),theNil)),new Env(e).With('_49_',new Lambda(new Pair(getSymbol('k'),theNil),new Pair(getSymbol('f'),new Pair(new Pair(new Pair(getSymbol('clone'),new Pair(getSymbol('_50_'),theNil)),new Pair(getSymbol('winders'),theNil)),theNil)),new Env(e).With('_50_',new Lambda(new Pair(getSymbol('save'),theNil),new Pair(getSymbol('clone'),new Pair(getSymbol('_51_'),theNil)),new Env(e).With('_51_',new Lambda(getSymbol('x'),new Pair(getSymbol('begin'),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('not'),new Pair(new Pair(getSymbol('eq?'),new Pair(getSymbol('save'),new Pair(getSymbol('winders'),theNil))),theNil)),new Pair(new Pair(getSymbol('do-wind'),new Pair(getSymbol('save'),theNil)),theNil))),new Pair(new Pair(getSymbol('apply'),new Pair(getSymbol('k'),new Pair(getSymbol('x'),theNil))),theNil))),e,function(list){var r,e=new Env(this.env);while(true){e['x']=list;r=((((isEq(e.parentEnv['save'],e.parentEnv.parentEnv.parentEnv.parentEnv.parentEnv.parentEnv.parentEnv.parentEnv.parentEnv['winders'])==false))!=false?Apply(e.parentEnv.parentEnv.parentEnv.parentEnv.parentEnv.parentEnv.parentEnv.parentEnv.parentEnv['do-wind'],new Pair(e.parentEnv['save'],theNil)):null),TC(e.parentEnv.parentEnv.parentEnv['k'],list=e['x'].ListCopy()));if(r!=theTC||r.f!=this)return r}})),function(list){var r,e=new Env(this.env);while(true){e['save']=list.car;r=e.parentEnv['_51_'].clone(e);if(r!=theTC||r.f!=this)return r}})),function(list){var r,e=new Env(this.env);while(true){e['k']=list.car;r=TC(e.parentEnv.parentEnv['f'],list=new Pair(Apply(e.parentEnv['_50_'].clone(e),new Pair(e.parentEnv.parentEnv.parentEnv.parentEnv.parentEnv.parentEnv['winders'],theNil)),theNil));if(r!=theTC||r.f!=this)return r}})),function(list){var r,e=new Env(this.env);while(true){e['f']=list.car;r=TC(e.parentEnv.parentEnv['c'],list=new Pair(e.parentEnv['_49_'].clone(e),theNil));if(r!=theTC||r.f!=this)return r}})),function(list){var r,e=new Env(this.env);while(true){e['c']=list.car;r=e.set('call/cc',e.parentEnv['_48_'].clone(e));if(r!=theTC||r.f!=this)return r}})).With('_44_',new Lambda(new Pair(getSymbol('in'),new Pair(getSymbol('body'),new Pair(getSymbol('out'),theNil))),new Pair(getSymbol('begin'),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('ans'),new Pair(false,theNil))),new Pair(new Pair(getSymbol('in'),theNil),new Pair(new Pair(getSymbol('set!'),new Pair(getSymbol('winders'),new Pair(new Pair(getSymbol('cons'),new Pair(new Pair(getSymbol('cons'),new Pair(getSymbol('in'),new Pair(getSymbol('out'),theNil))),new Pair(getSymbol('winders'),theNil))),theNil))),new Pair(new Pair(getSymbol('set!'),new Pair(getSymbol('ans'),new Pair(new Pair(getSymbol('body'),theNil),theNil))),new Pair(new Pair(getSymbol('set!'),new Pair(getSymbol('winders'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('winders'),theNil)),theNil))),new Pair(new Pair(getSymbol('out'),theNil),new Pair(getSymbol('ans'),theNil)))))))),e,function(list){var r,e=new Env(this.env);while(true){e['in']=list.car;e['body']=list.cdr.car;e['out']=list.cdr.cdr.car;r=(e['ans']=false,Apply(e['in'],theNil),e.set('winders',new Pair(new Pair(e['in'],e['out']),e.parentEnv['winders'])),e['ans']=Apply(e['body'],theNil),e.set('winders',e.parentEnv['winders'].cdr),Apply(e['out'],theNil),e['ans']);if(r!=theTC||r.f!=this)return r}})),function(list){var r,e=new Env(this.env);while(true){r=(e['winders']=theNil,e['common-tail']=e.parentEnv['_41_'].clone(e),e['do-wind']=e.parentEnv['_42_'].clone(e),Apply(e.parentEnv['_43_'].clone(e),new Pair(TopEnv.get('call/cc'),theNil)),e.set('call-with-current-continuation',TopEnv.get('call/cc')),e.set('dynamic-wind',e.parentEnv['_44_'].clone(e)));if(r!=theTC||r.f!=this)return r}}),theNil);
e['js-char']=new Lambda(new Pair(getSymbol('c'),theNil),new Pair(getSymbol('begin'),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('char-code'),new Pair(new Pair(getSymbol('char->integer'),new Pair(getSymbol('c'),theNil)),theNil))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('>='),new Pair(getSymbol('char-code'),new Pair(32,theNil))),new Pair(new Pair(getSymbol('string'),new Pair(getSymbol('c'),theNil)),new Pair(new Pair(getSymbol('string-append'),new Pair("\\x",new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('<'),new Pair(getSymbol('char-code'),new Pair(16,theNil))),new Pair("0",new Pair("",theNil)))),new Pair(new Pair(getSymbol('number->string'),new Pair(getSymbol('char-code'),new Pair(16,theNil))),theNil)))),theNil)))),theNil))),e,function(list){var r,e=new Env(this.env);while(true){e['c']=list.car;r=(e['char-code']=Apply(TopEnv.get('char->integer'),new Pair(e['c'],theNil)),((e['char-code']>=32)!=false?TC(TopEnv.get('string'),list=new Pair(e['c'],theNil)):("\\x"+((e['char-code']<16)!=false?"0":"")+Apply(TopEnv.get('number->string'),new Pair(e['char-code'],new Pair(16,theNil))))));if(r!=theTC||r.f!=this)return r}});
e['compile']=new Lambda(new Pair(getSymbol('ex'),getSymbol('tt')),new Pair(getSymbol('begin'),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('tail'),new Pair(false,theNil))),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('locs'),new Pair(false,theNil))),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('app'),new Pair("Apply",theNil))),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('prefix'),new Pair("",theNil))),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('suffix'),new Pair("",theNil))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('not'),new Pair(new Pair(getSymbol('null?'),new Pair(getSymbol('tt'),theNil)),theNil)),new Pair(new Pair(getSymbol('begin'),new Pair(new Pair(getSymbol('set!'),new Pair(getSymbol('locs'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('tt'),theNil)),theNil))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('not'),new Pair(new Pair(getSymbol('null?'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('tt'),theNil)),theNil)),theNil)),new Pair(new Pair(getSymbol('begin'),new Pair(new Pair(getSymbol('set!'),new Pair(getSymbol('tail'),new Pair(new Pair(getSymbol('cadr'),new Pair(getSymbol('tt'),theNil)),theNil))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('not'),new Pair(new Pair(getSymbol('null?'),new Pair(new Pair(getSymbol('cddr'),new Pair(getSymbol('tt'),theNil)),theNil)),theNil)),new Pair(new Pair(getSymbol('begin'),new Pair(new Pair(getSymbol('set!'),new Pair(getSymbol('prefix'),new Pair(new Pair(getSymbol('caddr'),new Pair(getSymbol('tt'),theNil)),theNil))),new Pair(new Pair(getSymbol('set!'),new Pair(getSymbol('suffix'),new Pair(new Pair(getSymbol('cadddr'),new Pair(getSymbol('tt'),theNil)),theNil))),theNil))),theNil))),theNil))),theNil))),theNil))),theNil))),new Pair(new Pair(getSymbol('if'),new Pair(getSymbol('tail'),new Pair(new Pair(getSymbol('set!'),new Pair(getSymbol('app'),new Pair("TC",theNil))),theNil))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('number?'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('string-append'),new Pair(getSymbol('prefix'),new Pair(new Pair(getSymbol('number->string'),new Pair(getSymbol('ex'),theNil)),new Pair(getSymbol('suffix'),theNil)))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('symbol?'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('if'),new Pair(getSymbol('locs'),new Pair(new Pair(getSymbol('string-append'),new Pair(getSymbol('prefix'),new Pair(new Pair(getSymbol('locs'),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('gen'),theNil)),new Pair(getSymbol('ex'),new Pair("e",theNil)))),new Pair(getSymbol('suffix'),theNil)))),new Pair(new Pair(getSymbol('string-append'),new Pair(getSymbol('prefix'),new Pair("e.get('",new Pair(new Pair(getSymbol('symbol->string'),new Pair(getSymbol('ex'),theNil)),new Pair("')",new Pair(getSymbol('suffix'),theNil)))))),theNil)))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('string?'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('string-append'),new Pair(getSymbol('prefix'),new Pair(new Pair(getSymbol('str'),new Pair(getSymbol('ex'),theNil)),new Pair(getSymbol('suffix'),theNil)))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('char?'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('string-append'),new Pair(getSymbol('prefix'),new Pair("getChar('",new Pair(new Pair(getSymbol('js-char'),new Pair(getSymbol('ex'),theNil)),new Pair("')",new Pair(getSymbol('suffix'),theNil)))))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('null?'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('error'),new Pair("cannot compile ()",theNil)),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('boolean?'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('string-append'),new Pair(getSymbol('prefix'),new Pair(new Pair(getSymbol('if'),new Pair(getSymbol('ex'),new Pair("true",new Pair("false",theNil)))),new Pair(getSymbol('suffix'),theNil)))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('vector?'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('string-append'),new Pair(getSymbol('prefix'),new Pair(getSymbol('app'),new Pair("(e.get('list->vector'),",new Pair(new Pair(getSymbol('if'),new Pair(getSymbol('tail'),new Pair("list=",new Pair("",theNil)))),new Pair("new Pair(",new Pair(new Pair(getSymbol('compile-quote'),new Pair(new Pair(getSymbol('vector->list'),new Pair(getSymbol('ex'),theNil)),theNil)),new Pair(",theNil),e)",new Pair(getSymbol('suffix'),theNil))))))))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('not'),new Pair(new Pair(getSymbol('pair?'),new Pair(getSymbol('ex'),theNil)),theNil)),new Pair(new Pair(getSymbol('error'),new Pair(new Pair(getSymbol('string-append'),new Pair("cannot compile ",new Pair(new Pair(getSymbol('str'),new Pair(getSymbol('ex'),theNil)),theNil))),theNil)),new Pair(new Pair(getSymbol('compile-pair'),new Pair(getSymbol('ex'),new Pair(getSymbol('locs'),new Pair(getSymbol('tail'),new Pair(getSymbol('prefix'),new Pair(getSymbol('suffix'),new Pair(getSymbol('app'),theNil))))))),theNil)))),theNil)))),theNil)))),theNil)))),theNil)))),theNil)))),theNil)))),theNil)))),theNil))))))))),e,function(list){var r,e=new Env(this.env);while(true){e['ex']=list.car;e['tt']=list.cdr;r=(e['tail']=false,e['locs']=false,e['app']="Apply",e['prefix']="",e['suffix']="",((((e['tt']==theNil)==false))!=false?(e['locs']=e['tt'].car,((((e['tt'].cdr==theNil)==false))!=false?(e['tail']=e['tt'].cdr.car,((((e['tt'].cdr.cdr==theNil)==false))!=false?(e['prefix']=e['tt'].cdr.cdr.car,e['suffix']=e['tt'].cdr.cdr.cdr.car):null)):null)):null),((e['tail'])!=false?e['app']="TC":null),(((typeof(e['ex'])=='number'))!=false?(e['prefix']+Apply(TopEnv.get('number->string'),new Pair(e['ex'],theNil))+e['suffix']):((((e['ex'])instanceof Symbol))!=false?((e['locs'])!=false?(e['prefix']+Apply(e['locs'],new Pair(getSymbol('gen'),new Pair(e['ex'],new Pair("e",theNil))))+e['suffix']):(e['prefix']+"e.get('"+e['ex'].name+"')"+e['suffix'])):(((typeof(e['ex'])=='string'))!=false?(e['prefix']+Str(e['ex'])+e['suffix']):((((e['ex'])instanceof Char))!=false?(e['prefix']+"getChar('"+Apply(TopEnv.get('js-char'),new Pair(e['ex'],theNil))+"')"+e['suffix']):(((e['ex']==theNil))!=false?TC(TopEnv.get('error'),list=new Pair("cannot compile ()",theNil)):(((typeof(e['ex'])=='boolean'))!=false?(e['prefix']+((e['ex'])!=false?"true":"false")+e['suffix']):((Apply(TopEnv.get('vector?'),new Pair(e['ex'],theNil)))!=false?(e['prefix']+e['app']+"(e.get('list->vector'),"+((e['tail'])!=false?"list=":"")+"new Pair("+Apply(TopEnv.get('compile-quote'),new Pair(Apply(TopEnv.get('vector->list'),new Pair(e['ex'],theNil)),theNil))+",theNil),e)"+e['suffix']):(((((e['ex'])instanceof Pair)==false))!=false?TC(TopEnv.get('error'),list=new Pair(("cannot compile "+Str(e['ex'])),theNil)):TC(TopEnv.get('compile-pair'),list=new Pair(e['ex'],new Pair(e['locs'],new Pair(e['tail'],new Pair(e['prefix'],new Pair(e['suffix'],new Pair(e['app'],theNil))))))))))))))));if(r!=theTC||r.f!=this)return r}});
e['compile-pair']=new Lambda(new Pair(getSymbol('ex'),new Pair(getSymbol('locs'),new Pair(getSymbol('tail'),new Pair(getSymbol('prefix'),new Pair(getSymbol('suffix'),new Pair(getSymbol('app'),theNil)))))),new Pair(getSymbol('begin'),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('list-len'),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('pair?'),new Pair(getSymbol('locs'),theNil)),new Pair(new Pair(getSymbol('length'),new Pair(getSymbol('locs'),theNil)),new Pair(false,theNil)))),theNil))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eq?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('begin'),theNil)),theNil))),new Pair(new Pair(getSymbol('compile-begin'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('ex'),theNil)),new Pair(getSymbol('locs'),new Pair(getSymbol('tail'),new Pair(getSymbol('prefix'),new Pair(getSymbol('suffix'),theNil)))))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eq?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('quote'),theNil)),theNil))),new Pair(new Pair(getSymbol('compile-quote'),new Pair(new Pair(getSymbol('cadr'),new Pair(getSymbol('ex'),theNil)),new Pair(getSymbol('prefix'),new Pair(getSymbol('suffix'),theNil)))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eq?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('not'),theNil)),theNil))),new Pair(new Pair(getSymbol('compile'),new Pair(new Pair(getSymbol('cadr'),new Pair(getSymbol('ex'),theNil)),new Pair(getSymbol('locs'),new Pair(false,new Pair(new Pair(getSymbol('string-append'),new Pair(getSymbol('prefix'),new Pair("(",theNil))),new Pair(new Pair(getSymbol('string-append'),new Pair("==false)",new Pair(getSymbol('suffix'),theNil))),theNil)))))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eq?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('symbol->string'),theNil)),theNil))),new Pair(new Pair(getSymbol('compile'),new Pair(new Pair(getSymbol('cadr'),new Pair(getSymbol('ex'),theNil)),new Pair(getSymbol('locs'),new Pair(false,new Pair(getSymbol('prefix'),new Pair(new Pair(getSymbol('string-append'),new Pair(getSymbol('suffix'),new Pair(".name",theNil))),theNil)))))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eq?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('car'),theNil)),theNil))),new Pair(new Pair(getSymbol('string-append'),new Pair(getSymbol('prefix'),new Pair(new Pair(getSymbol('compile'),new Pair(new Pair(getSymbol('cadr'),new Pair(getSymbol('ex'),theNil)),new Pair(getSymbol('locs'),theNil))),new Pair(".car",new Pair(getSymbol('suffix'),theNil))))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eq?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('cdr'),theNil)),theNil))),new Pair(new Pair(getSymbol('string-append'),new Pair(getSymbol('prefix'),new Pair(new Pair(getSymbol('compile'),new Pair(new Pair(getSymbol('cadr'),new Pair(getSymbol('ex'),theNil)),new Pair(getSymbol('locs'),theNil))),new Pair(".cdr",new Pair(getSymbol('suffix'),theNil))))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eq?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('caar'),theNil)),theNil))),new Pair(new Pair(getSymbol('string-append'),new Pair(getSymbol('prefix'),new Pair(new Pair(getSymbol('compile'),new Pair(new Pair(getSymbol('cadr'),new Pair(getSymbol('ex'),theNil)),new Pair(getSymbol('locs'),theNil))),new Pair(".car.car",new Pair(getSymbol('suffix'),theNil))))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eq?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('cadr'),theNil)),theNil))),new Pair(new Pair(getSymbol('string-append'),new Pair(getSymbol('prefix'),new Pair(new Pair(getSymbol('compile'),new Pair(new Pair(getSymbol('cadr'),new Pair(getSymbol('ex'),theNil)),new Pair(getSymbol('locs'),theNil))),new Pair(".cdr.car",new Pair(getSymbol('suffix'),theNil))))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eq?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('cdar'),theNil)),theNil))),new Pair(new Pair(getSymbol('string-append'),new Pair(getSymbol('prefix'),new Pair(new Pair(getSymbol('compile'),new Pair(new Pair(getSymbol('cadr'),new Pair(getSymbol('ex'),theNil)),new Pair(getSymbol('locs'),theNil))),new Pair(".car.cdr",new Pair(getSymbol('suffix'),theNil))))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eq?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('cddr'),theNil)),theNil))),new Pair(new Pair(getSymbol('string-append'),new Pair(getSymbol('prefix'),new Pair(new Pair(getSymbol('compile'),new Pair(new Pair(getSymbol('cadr'),new Pair(getSymbol('ex'),theNil)),new Pair(getSymbol('locs'),theNil))),new Pair(".cdr.cdr",new Pair(getSymbol('suffix'),theNil))))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eq?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('caaar'),theNil)),theNil))),new Pair(new Pair(getSymbol('string-append'),new Pair(getSymbol('prefix'),new Pair(new Pair(getSymbol('compile'),new Pair(new Pair(getSymbol('cadr'),new Pair(getSymbol('ex'),theNil)),new Pair(getSymbol('locs'),theNil))),new Pair(".car.car.car",new Pair(getSymbol('suffix'),theNil))))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eq?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('caddr'),theNil)),theNil))),new Pair(new Pair(getSymbol('string-append'),new Pair(getSymbol('prefix'),new Pair(new Pair(getSymbol('compile'),new Pair(new Pair(getSymbol('cadr'),new Pair(getSymbol('ex'),theNil)),new Pair(getSymbol('locs'),theNil))),new Pair(".cdr.cdr.car",new Pair(getSymbol('suffix'),theNil))))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eq?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('cdaar'),theNil)),theNil))),new Pair(new Pair(getSymbol('string-append'),new Pair(getSymbol('prefix'),new Pair(new Pair(getSymbol('compile'),new Pair(new Pair(getSymbol('cadr'),new Pair(getSymbol('ex'),theNil)),new Pair(getSymbol('locs'),theNil))),new Pair(".car.car.cdr",new Pair(getSymbol('suffix'),theNil))))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eq?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('cdddr'),theNil)),theNil))),new Pair(new Pair(getSymbol('string-append'),new Pair(getSymbol('prefix'),new Pair(new Pair(getSymbol('compile'),new Pair(new Pair(getSymbol('cadr'),new Pair(getSymbol('ex'),theNil)),new Pair(getSymbol('locs'),theNil))),new Pair(".cdr.cdr.cdr",new Pair(getSymbol('suffix'),theNil))))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eq?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('caaddr'),theNil)),theNil))),new Pair(new Pair(getSymbol('string-append'),new Pair(getSymbol('prefix'),new Pair(new Pair(getSymbol('compile'),new Pair(new Pair(getSymbol('cadr'),new Pair(getSymbol('ex'),theNil)),new Pair(getSymbol('locs'),theNil))),new Pair(".cdr.cdr.car.car",new Pair(getSymbol('suffix'),theNil))))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eq?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('cadddr'),theNil)),theNil))),new Pair(new Pair(getSymbol('string-append'),new Pair(getSymbol('prefix'),new Pair(new Pair(getSymbol('compile'),new Pair(new Pair(getSymbol('cadr'),new Pair(getSymbol('ex'),theNil)),new Pair(getSymbol('locs'),theNil))),new Pair(".cdr.cdr.cdr.car",new Pair(getSymbol('suffix'),theNil))))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eq?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('cdaddr'),theNil)),theNil))),new Pair(new Pair(getSymbol('string-append'),new Pair(getSymbol('prefix'),new Pair(new Pair(getSymbol('compile'),new Pair(new Pair(getSymbol('cadr'),new Pair(getSymbol('ex'),theNil)),new Pair(getSymbol('locs'),theNil))),new Pair(".cdr.cdr.car.cdr",new Pair(getSymbol('suffix'),theNil))))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eq?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('cddddr'),theNil)),theNil))),new Pair(new Pair(getSymbol('string-append'),new Pair(getSymbol('prefix'),new Pair(new Pair(getSymbol('compile'),new Pair(new Pair(getSymbol('cadr'),new Pair(getSymbol('ex'),theNil)),new Pair(getSymbol('locs'),theNil))),new Pair(".cdr.cdr.cdr.cdr",new Pair(getSymbol('suffix'),theNil))))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eq?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('cons'),theNil)),theNil))),new Pair(new Pair(getSymbol('string-append'),new Pair(getSymbol('prefix'),new Pair("new Pair(",new Pair(new Pair(getSymbol('compile'),new Pair(new Pair(getSymbol('cadr'),new Pair(getSymbol('ex'),theNil)),new Pair(getSymbol('locs'),theNil))),new Pair(",",new Pair(new Pair(getSymbol('compile'),new Pair(new Pair(getSymbol('caddr'),new Pair(getSymbol('ex'),theNil)),new Pair(getSymbol('locs'),theNil))),new Pair(")",new Pair(getSymbol('suffix'),theNil)))))))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eq?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('boolean?'),theNil)),theNil))),new Pair(new Pair(getSymbol('string-append'),new Pair(getSymbol('prefix'),new Pair("(typeof(",new Pair(new Pair(getSymbol('compile'),new Pair(new Pair(getSymbol('cadr'),new Pair(getSymbol('ex'),theNil)),new Pair(getSymbol('locs'),theNil))),new Pair(")=='boolean')",new Pair(getSymbol('suffix'),theNil)))))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eq?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('string?'),theNil)),theNil))),new Pair(new Pair(getSymbol('string-append'),new Pair(getSymbol('prefix'),new Pair("(typeof(",new Pair(new Pair(getSymbol('compile'),new Pair(new Pair(getSymbol('cadr'),new Pair(getSymbol('ex'),theNil)),new Pair(getSymbol('locs'),theNil))),new Pair(")=='string')",new Pair(getSymbol('suffix'),theNil)))))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eq?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('number?'),theNil)),theNil))),new Pair(new Pair(getSymbol('string-append'),new Pair(getSymbol('prefix'),new Pair("(typeof(",new Pair(new Pair(getSymbol('compile'),new Pair(new Pair(getSymbol('cadr'),new Pair(getSymbol('ex'),theNil)),new Pair(getSymbol('locs'),theNil))),new Pair(")=='number')",new Pair(getSymbol('suffix'),theNil)))))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eq?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('char?'),theNil)),theNil))),new Pair(new Pair(getSymbol('string-append'),new Pair(getSymbol('prefix'),new Pair("((",new Pair(new Pair(getSymbol('compile'),new Pair(new Pair(getSymbol('cadr'),new Pair(getSymbol('ex'),theNil)),new Pair(getSymbol('locs'),theNil))),new Pair(")instanceof Char)",new Pair(getSymbol('suffix'),theNil)))))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eq?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('symbol?'),theNil)),theNil))),new Pair(new Pair(getSymbol('string-append'),new Pair(getSymbol('prefix'),new Pair("((",new Pair(new Pair(getSymbol('compile'),new Pair(new Pair(getSymbol('cadr'),new Pair(getSymbol('ex'),theNil)),new Pair(getSymbol('locs'),theNil))),new Pair(")instanceof Symbol)",new Pair(getSymbol('suffix'),theNil)))))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eq?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('syntax?'),theNil)),theNil))),new Pair(new Pair(getSymbol('string-append'),new Pair(getSymbol('prefix'),new Pair("((",new Pair(new Pair(getSymbol('compile'),new Pair(new Pair(getSymbol('cadr'),new Pair(getSymbol('ex'),theNil)),new Pair(getSymbol('locs'),theNil))),new Pair(")instanceof Syntax)",new Pair(getSymbol('suffix'),theNil)))))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eq?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('null?'),theNil)),theNil))),new Pair(new Pair(getSymbol('string-append'),new Pair(getSymbol('prefix'),new Pair("(",new Pair(new Pair(getSymbol('compile'),new Pair(new Pair(getSymbol('cadr'),new Pair(getSymbol('ex'),theNil)),new Pair(getSymbol('locs'),theNil))),new Pair("==theNil)",new Pair(getSymbol('suffix'),theNil)))))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eq?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('pair?'),theNil)),theNil))),new Pair(new Pair(getSymbol('string-append'),new Pair(getSymbol('prefix'),new Pair("((",new Pair(new Pair(getSymbol('compile'),new Pair(new Pair(getSymbol('cadr'),new Pair(getSymbol('ex'),theNil)),new Pair(getSymbol('locs'),theNil))),new Pair(")instanceof Pair)",new Pair(getSymbol('suffix'),theNil)))))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eq?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('str'),theNil)),theNil))),new Pair(new Pair(getSymbol('string-append'),new Pair(getSymbol('prefix'),new Pair("Str(",new Pair(new Pair(getSymbol('compile'),new Pair(new Pair(getSymbol('cadr'),new Pair(getSymbol('ex'),theNil)),new Pair(getSymbol('locs'),theNil))),new Pair(")",new Pair(getSymbol('suffix'),theNil)))))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eq?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('clone'),theNil)),theNil))),new Pair(new Pair(getSymbol('string-append'),new Pair(getSymbol('prefix'),new Pair(new Pair(getSymbol('compile'),new Pair(new Pair(getSymbol('cadr'),new Pair(getSymbol('ex'),theNil)),new Pair(getSymbol('locs'),theNil))),new Pair(".clone(e)",new Pair(getSymbol('suffix'),theNil))))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eq?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('get-prop'),theNil)),theNil))),new Pair(new Pair(getSymbol('string-append'),new Pair(getSymbol('prefix'),new Pair(new Pair(getSymbol('compile'),new Pair(new Pair(getSymbol('cadr'),new Pair(getSymbol('ex'),theNil)),new Pair(getSymbol('locs'),theNil))),new Pair("[",new Pair(new Pair(getSymbol('str'),new Pair(new Pair(getSymbol('caddr'),new Pair(getSymbol('ex'),theNil)),theNil)),new Pair("]",new Pair(getSymbol('suffix'),theNil))))))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eq?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('>'),theNil)),theNil))),new Pair(true,new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eq?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('<'),theNil)),theNil))),new Pair(true,new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eq?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('>='),theNil)),theNil))),new Pair(true,new Pair(new Pair(getSymbol('eq?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('<='),theNil)),theNil))),theNil)))),theNil)))),theNil)))),new Pair(new Pair(getSymbol('string-append'),new Pair(getSymbol('prefix'),new Pair(new Pair(getSymbol('compile-predicate'),new Pair(new Pair(getSymbol('symbol->string'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),theNil)),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('ex'),theNil)),new Pair(getSymbol('locs'),theNil)))),new Pair(getSymbol('suffix'),theNil)))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eq?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('+'),theNil)),theNil))),new Pair(new Pair(getSymbol('string-append'),new Pair(getSymbol('prefix'),new Pair(new Pair(getSymbol('compile-append'),new Pair("0",new Pair("+",new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('ex'),theNil)),new Pair(getSymbol('locs'),theNil))))),new Pair(getSymbol('suffix'),theNil)))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eq?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('*'),theNil)),theNil))),new Pair(new Pair(getSymbol('string-append'),new Pair(getSymbol('prefix'),new Pair(new Pair(getSymbol('compile-append'),new Pair("1",new Pair("*",new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('ex'),theNil)),new Pair(getSymbol('locs'),theNil))))),new Pair(getSymbol('suffix'),theNil)))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eq?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('-'),theNil)),theNil))),new Pair(new Pair(getSymbol('string-append'),new Pair(getSymbol('prefix'),new Pair(new Pair(getSymbol('compile-minus'),new Pair("-",new Pair("-",new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('ex'),theNil)),new Pair(getSymbol('locs'),theNil))))),new Pair(getSymbol('suffix'),theNil)))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eq?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('/'),theNil)),theNil))),new Pair(new Pair(getSymbol('string-append'),new Pair(getSymbol('prefix'),new Pair(new Pair(getSymbol('compile-minus'),new Pair("1/",new Pair("/",new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('ex'),theNil)),new Pair(getSymbol('locs'),theNil))))),new Pair(getSymbol('suffix'),theNil)))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eq?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('string-append'),theNil)),theNil))),new Pair(new Pair(getSymbol('string-append'),new Pair(getSymbol('prefix'),new Pair(new Pair(getSymbol('compile-append'),new Pair("''",new Pair("+",new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('ex'),theNil)),new Pair(getSymbol('locs'),theNil))))),new Pair(getSymbol('suffix'),theNil)))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eq?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('eq?'),theNil)),theNil))),new Pair(true,new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eq?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('='),theNil)),theNil))),new Pair(true,new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eq?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('eqv?'),theNil)),theNil))),new Pair(true,new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eq?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('string=?'),theNil)),theNil))),new Pair(true,new Pair(new Pair(getSymbol('eq?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('char=?'),theNil)),theNil))),theNil)))),theNil)))),theNil)))),theNil)))),new Pair(new Pair(getSymbol('string-append'),new Pair(getSymbol('prefix'),new Pair("isEq(",new Pair(new Pair(getSymbol('compile'),new Pair(new Pair(getSymbol('cadr'),new Pair(getSymbol('ex'),theNil)),new Pair(getSymbol('locs'),theNil))),new Pair(",",new Pair(new Pair(getSymbol('compile'),new Pair(new Pair(getSymbol('caddr'),new Pair(getSymbol('ex'),theNil)),new Pair(getSymbol('locs'),theNil))),new Pair(")",new Pair(getSymbol('suffix'),theNil)))))))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eq?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('list'),theNil)),theNil))),new Pair(new Pair(getSymbol('string-append'),new Pair(getSymbol('prefix'),new Pair(new Pair(getSymbol('compile-list'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('ex'),theNil)),new Pair(getSymbol('locs'),theNil))),new Pair(getSymbol('suffix'),theNil)))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eq?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('if'),theNil)),theNil))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('null?'),new Pair(new Pair(getSymbol('cdddr'),new Pair(getSymbol('ex'),theNil)),theNil)),new Pair(new Pair(getSymbol('compile'),new Pair(new Pair(getSymbol('caddr'),new Pair(getSymbol('ex'),theNil)),new Pair(getSymbol('locs'),new Pair(getSymbol('tail'),new Pair(new Pair(getSymbol('string-append'),new Pair(getSymbol('prefix'),new Pair("((",new Pair(new Pair(getSymbol('compile'),new Pair(new Pair(getSymbol('cadr'),new Pair(getSymbol('ex'),theNil)),new Pair(getSymbol('locs'),theNil))),new Pair(")!=false?",theNil))))),new Pair(new Pair(getSymbol('string-append'),new Pair(":null)",new Pair(getSymbol('suffix'),theNil))),theNil)))))),new Pair(new Pair(getSymbol('compile'),new Pair(new Pair(getSymbol('cadddr'),new Pair(getSymbol('ex'),theNil)),new Pair(getSymbol('locs'),new Pair(getSymbol('tail'),new Pair(new Pair(getSymbol('string-append'),new Pair(getSymbol('prefix'),new Pair("((",new Pair(new Pair(getSymbol('compile'),new Pair(new Pair(getSymbol('cadr'),new Pair(getSymbol('ex'),theNil)),new Pair(getSymbol('locs'),theNil))),new Pair(")!=false?",new Pair(new Pair(getSymbol('compile'),new Pair(new Pair(getSymbol('caddr'),new Pair(getSymbol('ex'),theNil)),new Pair(getSymbol('locs'),new Pair(getSymbol('tail'),theNil)))),new Pair(":",theNil))))))),new Pair(new Pair(getSymbol('string-append'),new Pair(")",new Pair(getSymbol('suffix'),theNil))),theNil)))))),theNil)))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eq?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('define-syntax'),theNil)),theNil))),new Pair(new Pair(getSymbol('string-append'),new Pair(getSymbol('prefix'),new Pair("e['",new Pair(new Pair(getSymbol('symbol->string'),new Pair(new Pair(getSymbol('cadr'),new Pair(getSymbol('ex'),theNil)),theNil)),new Pair("']=new Syntax(e.get('",new Pair(new Pair(getSymbol('symbol->string'),new Pair(new Pair(getSymbol('caaddr'),new Pair(getSymbol('ex'),theNil)),theNil)),new Pair("'),",new Pair(new Pair(getSymbol('compile-quote'),new Pair(new Pair(getSymbol('cdaddr'),new Pair(getSymbol('ex'),theNil)),theNil)),new Pair(")",new Pair(getSymbol('suffix'),theNil)))))))))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eq?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('define'),theNil)),theNil))),new Pair(new Pair(getSymbol('symbol?'),new Pair(new Pair(getSymbol('cadr'),new Pair(getSymbol('ex'),theNil)),theNil)),new Pair(false,theNil)))),new Pair(new Pair(getSymbol('begin'),new Pair(new Pair(getSymbol('if'),new Pair(getSymbol('locs'),new Pair(new Pair(getSymbol('locs'),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('add'),theNil)),new Pair(new Pair(getSymbol('cadr'),new Pair(getSymbol('ex'),theNil)),theNil))),theNil))),new Pair(new Pair(getSymbol('string-append'),new Pair(getSymbol('prefix'),new Pair("e['",new Pair(new Pair(getSymbol('symbol->string'),new Pair(new Pair(getSymbol('cadr'),new Pair(getSymbol('ex'),theNil)),theNil)),new Pair("']=",new Pair(new Pair(getSymbol('compile'),new Pair(new Pair(getSymbol('caddr'),new Pair(getSymbol('ex'),theNil)),new Pair(getSymbol('locs'),theNil))),new Pair(getSymbol('suffix'),theNil))))))),theNil))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eq?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('set!'),theNil)),theNil))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('if'),new Pair(getSymbol('locs'),new Pair(new Pair(getSymbol('locs'),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('memq'),theNil)),new Pair(new Pair(getSymbol('cadr'),new Pair(getSymbol('ex'),theNil)),theNil))),new Pair(false,theNil)))),new Pair(new Pair(getSymbol('compile'),new Pair(new Pair(getSymbol('caddr'),new Pair(getSymbol('ex'),theNil)),new Pair(getSymbol('locs'),new Pair(false,new Pair(new Pair(getSymbol('string-append'),new Pair(getSymbol('prefix'),new Pair("e['",new Pair(new Pair(getSymbol('symbol->string'),new Pair(new Pair(getSymbol('cadr'),new Pair(getSymbol('ex'),theNil)),theNil)),new Pair("']=",theNil))))),new Pair(getSymbol('suffix'),theNil)))))),new Pair(new Pair(getSymbol('compile'),new Pair(new Pair(getSymbol('caddr'),new Pair(getSymbol('ex'),theNil)),new Pair(getSymbol('locs'),new Pair(false,new Pair(new Pair(getSymbol('string-append'),new Pair(getSymbol('prefix'),new Pair("e.set('",new Pair(new Pair(getSymbol('symbol->string'),new Pair(new Pair(getSymbol('cadr'),new Pair(getSymbol('ex'),theNil)),theNil)),new Pair("',",theNil))))),new Pair(new Pair(getSymbol('string-append'),new Pair(")",new Pair(getSymbol('suffix'),theNil))),theNil)))))),theNil)))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eq?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('lambda'),theNil)),theNil))),new Pair(new Pair(getSymbol('string-append'),new Pair(getSymbol('prefix'),new Pair(new Pair(getSymbol('compile-lambda-obj'),new Pair(new Pair(getSymbol('cadr'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('cddr'),new Pair(getSymbol('ex'),theNil)),new Pair(getSymbol('locs'),theNil)))),new Pair(getSymbol('suffix'),theNil)))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eq?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('define'),theNil)),theNil))),new Pair(new Pair(getSymbol('pair?'),new Pair(new Pair(getSymbol('cadr'),new Pair(getSymbol('ex'),theNil)),theNil)),new Pair(false,theNil)))),new Pair(new Pair(getSymbol('begin'),new Pair(new Pair(getSymbol('if'),new Pair(getSymbol('locs'),new Pair(new Pair(getSymbol('locs'),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('add'),theNil)),new Pair(new Pair(getSymbol('caadr'),new Pair(getSymbol('ex'),theNil)),theNil))),theNil))),new Pair(new Pair(getSymbol('string-append'),new Pair(getSymbol('prefix'),new Pair("e['",new Pair(new Pair(getSymbol('symbol->string'),new Pair(new Pair(getSymbol('caadr'),new Pair(getSymbol('ex'),theNil)),theNil)),new Pair("']=",new Pair(new Pair(getSymbol('compile-lambda-obj'),new Pair(new Pair(getSymbol('cdadr'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('cddr'),new Pair(getSymbol('ex'),theNil)),new Pair(getSymbol('locs'),theNil)))),new Pair(getSymbol('suffix'),theNil))))))),theNil))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eq?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('apply'),theNil)),theNil))),new Pair(new Pair(getSymbol('string-append'),new Pair(getSymbol('prefix'),new Pair(getSymbol('app'),new Pair("(",new Pair(new Pair(getSymbol('compile'),new Pair(new Pair(getSymbol('cadr'),new Pair(getSymbol('ex'),theNil)),new Pair(getSymbol('locs'),theNil))),new Pair(",",new Pair(new Pair(getSymbol('if'),new Pair(getSymbol('tail'),new Pair("list=",new Pair("",theNil)))),new Pair(new Pair(getSymbol('compile-apply-list'),new Pair(new Pair(getSymbol('cddr'),new Pair(getSymbol('ex'),theNil)),new Pair(getSymbol('locs'),theNil))),new Pair(")",new Pair(getSymbol('suffix'),theNil)))))))))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('if'),new Pair(getSymbol('tail'),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('number?'),new Pair(getSymbol('list-len'),theNil)),new Pair(new Pair(getSymbol('>='),new Pair(getSymbol('list-len'),new Pair(new Pair(getSymbol('length'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('ex'),theNil)),theNil)),theNil))),new Pair(false,theNil)))),new Pair(false,theNil)))),new Pair(new Pair(getSymbol('string-append'),new Pair(getSymbol('prefix'),new Pair("(",new Pair(new Pair(getSymbol('compile-reuse'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('ex'),theNil)),new Pair("list",new Pair(getSymbol('locs'),theNil)))),new Pair(",",new Pair("theTC.f=",new Pair(new Pair(getSymbol('compile'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),new Pair(getSymbol('locs'),theNil))),new Pair(",theTC.args=list,theTC)",new Pair(getSymbol('suffix'),theNil))))))))),new Pair(new Pair(getSymbol('compile-list'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('ex'),theNil)),new Pair(getSymbol('locs'),new Pair(new Pair(getSymbol('string-append'),new Pair(getSymbol('prefix'),new Pair(getSymbol('app'),new Pair("(",new Pair(new Pair(getSymbol('compile'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),new Pair(getSymbol('locs'),theNil))),new Pair(",",new Pair(new Pair(getSymbol('if'),new Pair(getSymbol('tail'),new Pair("list=",new Pair("",theNil)))),theNil))))))),new Pair(new Pair(getSymbol('string-append'),new Pair(")",new Pair(getSymbol('suffix'),theNil))),theNil))))),theNil)))),theNil)))),theNil)))),theNil)))),theNil)))),theNil)))),theNil)))),theNil)))),theNil)))),theNil)))),theNil)))),theNil)))),theNil)))),theNil)))),theNil)))),theNil)))),theNil)))),theNil)))),theNil)))),theNil)))),theNil)))),theNil)))),theNil)))),theNil)))),theNil)))),theNil)))),theNil)))),theNil)))),theNil)))),theNil)))),theNil)))),theNil)))),theNil)))),theNil)))),theNil)))),theNil)))),theNil)))),theNil)))),theNil)))),theNil)))),theNil)))),theNil)))),theNil)))),theNil)))),theNil)))),theNil)))),theNil))),e,function(list){var r,e=new Env(this.env);while(true){e['ex']=list.car;e['locs']=list.cdr.car;e['tail']=list.cdr.cdr.car;e['prefix']=list.cdr.cdr.cdr.car;e['suffix']=list.cdr.cdr.cdr.cdr.car;e['app']=list.cdr.cdr.cdr.cdr.cdr.car;r=(e['list-len']=((((e['locs'])instanceof Pair))!=false?Apply(TopEnv.get('length'),new Pair(e['locs'],theNil)):false),((isEq(e['ex'].car,getSymbol('begin')))!=false?TC(TopEnv.get('compile-begin'),list=new Pair(e['ex'].cdr,new Pair(e['locs'],new Pair(e['tail'],new Pair(e['prefix'],new Pair(e['suffix'],theNil)))))):((isEq(e['ex'].car,getSymbol('quote')))!=false?TC(TopEnv.get('compile-quote'),list=new Pair(e['ex'].cdr.car,new Pair(e['prefix'],new Pair(e['suffix'],theNil)))):((isEq(e['ex'].car,getSymbol('not')))!=false?TC(TopEnv.get('compile'),list=new Pair(e['ex'].cdr.car,new Pair(e['locs'],new Pair(false,new Pair((e['prefix']+"("),new Pair(("==false)"+e['suffix']),theNil)))))):((isEq(e['ex'].car,getSymbol('symbol->string')))!=false?TC(TopEnv.get('compile'),list=new Pair(e['ex'].cdr.car,new Pair(e['locs'],new Pair(false,new Pair(e['prefix'],new Pair((e['suffix']+".name"),theNil)))))):((isEq(e['ex'].car,getSymbol('car')))!=false?(e['prefix']+Apply(TopEnv.get('compile'),new Pair(e['ex'].cdr.car,new Pair(e['locs'],theNil)))+".car"+e['suffix']):((isEq(e['ex'].car,getSymbol('cdr')))!=false?(e['prefix']+Apply(TopEnv.get('compile'),new Pair(e['ex'].cdr.car,new Pair(e['locs'],theNil)))+".cdr"+e['suffix']):((isEq(e['ex'].car,getSymbol('caar')))!=false?(e['prefix']+Apply(TopEnv.get('compile'),new Pair(e['ex'].cdr.car,new Pair(e['locs'],theNil)))+".car.car"+e['suffix']):((isEq(e['ex'].car,getSymbol('cadr')))!=false?(e['prefix']+Apply(TopEnv.get('compile'),new Pair(e['ex'].cdr.car,new Pair(e['locs'],theNil)))+".cdr.car"+e['suffix']):((isEq(e['ex'].car,getSymbol('cdar')))!=false?(e['prefix']+Apply(TopEnv.get('compile'),new Pair(e['ex'].cdr.car,new Pair(e['locs'],theNil)))+".car.cdr"+e['suffix']):((isEq(e['ex'].car,getSymbol('cddr')))!=false?(e['prefix']+Apply(TopEnv.get('compile'),new Pair(e['ex'].cdr.car,new Pair(e['locs'],theNil)))+".cdr.cdr"+e['suffix']):((isEq(e['ex'].car,getSymbol('caaar')))!=false?(e['prefix']+Apply(TopEnv.get('compile'),new Pair(e['ex'].cdr.car,new Pair(e['locs'],theNil)))+".car.car.car"+e['suffix']):((isEq(e['ex'].car,getSymbol('caddr')))!=false?(e['prefix']+Apply(TopEnv.get('compile'),new Pair(e['ex'].cdr.car,new Pair(e['locs'],theNil)))+".cdr.cdr.car"+e['suffix']):((isEq(e['ex'].car,getSymbol('cdaar')))!=false?(e['prefix']+Apply(TopEnv.get('compile'),new Pair(e['ex'].cdr.car,new Pair(e['locs'],theNil)))+".car.car.cdr"+e['suffix']):((isEq(e['ex'].car,getSymbol('cdddr')))!=false?(e['prefix']+Apply(TopEnv.get('compile'),new Pair(e['ex'].cdr.car,new Pair(e['locs'],theNil)))+".cdr.cdr.cdr"+e['suffix']):((isEq(e['ex'].car,getSymbol('caaddr')))!=false?(e['prefix']+Apply(TopEnv.get('compile'),new Pair(e['ex'].cdr.car,new Pair(e['locs'],theNil)))+".cdr.cdr.car.car"+e['suffix']):((isEq(e['ex'].car,getSymbol('cadddr')))!=false?(e['prefix']+Apply(TopEnv.get('compile'),new Pair(e['ex'].cdr.car,new Pair(e['locs'],theNil)))+".cdr.cdr.cdr.car"+e['suffix']):((isEq(e['ex'].car,getSymbol('cdaddr')))!=false?(e['prefix']+Apply(TopEnv.get('compile'),new Pair(e['ex'].cdr.car,new Pair(e['locs'],theNil)))+".cdr.cdr.car.cdr"+e['suffix']):((isEq(e['ex'].car,getSymbol('cddddr')))!=false?(e['prefix']+Apply(TopEnv.get('compile'),new Pair(e['ex'].cdr.car,new Pair(e['locs'],theNil)))+".cdr.cdr.cdr.cdr"+e['suffix']):((isEq(e['ex'].car,getSymbol('cons')))!=false?(e['prefix']+"new Pair("+Apply(TopEnv.get('compile'),new Pair(e['ex'].cdr.car,new Pair(e['locs'],theNil)))+","+Apply(TopEnv.get('compile'),new Pair(e['ex'].cdr.cdr.car,new Pair(e['locs'],theNil)))+")"+e['suffix']):((isEq(e['ex'].car,getSymbol('boolean?')))!=false?(e['prefix']+"(typeof("+Apply(TopEnv.get('compile'),new Pair(e['ex'].cdr.car,new Pair(e['locs'],theNil)))+")=='boolean')"+e['suffix']):((isEq(e['ex'].car,getSymbol('string?')))!=false?(e['prefix']+"(typeof("+Apply(TopEnv.get('compile'),new Pair(e['ex'].cdr.car,new Pair(e['locs'],theNil)))+")=='string')"+e['suffix']):((isEq(e['ex'].car,getSymbol('number?')))!=false?(e['prefix']+"(typeof("+Apply(TopEnv.get('compile'),new Pair(e['ex'].cdr.car,new Pair(e['locs'],theNil)))+")=='number')"+e['suffix']):((isEq(e['ex'].car,getSymbol('char?')))!=false?(e['prefix']+"(("+Apply(TopEnv.get('compile'),new Pair(e['ex'].cdr.car,new Pair(e['locs'],theNil)))+")instanceof Char)"+e['suffix']):((isEq(e['ex'].car,getSymbol('symbol?')))!=false?(e['prefix']+"(("+Apply(TopEnv.get('compile'),new Pair(e['ex'].cdr.car,new Pair(e['locs'],theNil)))+")instanceof Symbol)"+e['suffix']):((isEq(e['ex'].car,getSymbol('syntax?')))!=false?(e['prefix']+"(("+Apply(TopEnv.get('compile'),new Pair(e['ex'].cdr.car,new Pair(e['locs'],theNil)))+")instanceof Syntax)"+e['suffix']):((isEq(e['ex'].car,getSymbol('null?')))!=false?(e['prefix']+"("+Apply(TopEnv.get('compile'),new Pair(e['ex'].cdr.car,new Pair(e['locs'],theNil)))+"==theNil)"+e['suffix']):((isEq(e['ex'].car,getSymbol('pair?')))!=false?(e['prefix']+"(("+Apply(TopEnv.get('compile'),new Pair(e['ex'].cdr.car,new Pair(e['locs'],theNil)))+")instanceof Pair)"+e['suffix']):((isEq(e['ex'].car,getSymbol('str')))!=false?(e['prefix']+"Str("+Apply(TopEnv.get('compile'),new Pair(e['ex'].cdr.car,new Pair(e['locs'],theNil)))+")"+e['suffix']):((isEq(e['ex'].car,getSymbol('clone')))!=false?(e['prefix']+Apply(TopEnv.get('compile'),new Pair(e['ex'].cdr.car,new Pair(e['locs'],theNil)))+".clone(e)"+e['suffix']):((isEq(e['ex'].car,getSymbol('get-prop')))!=false?(e['prefix']+Apply(TopEnv.get('compile'),new Pair(e['ex'].cdr.car,new Pair(e['locs'],theNil)))+"["+Str(e['ex'].cdr.cdr.car)+"]"+e['suffix']):((((isEq(e['ex'].car,getSymbol('>')))!=false?true:((isEq(e['ex'].car,getSymbol('<')))!=false?true:((isEq(e['ex'].car,getSymbol('>=')))!=false?true:isEq(e['ex'].car,getSymbol('<='))))))!=false?(e['prefix']+Apply(TopEnv.get('compile-predicate'),new Pair(e['ex'].car.name,new Pair(e['ex'].cdr,new Pair(e['locs'],theNil))))+e['suffix']):((isEq(e['ex'].car,getSymbol('+')))!=false?(e['prefix']+Apply(TopEnv.get('compile-append'),new Pair("0",new Pair("+",new Pair(e['ex'].cdr,new Pair(e['locs'],theNil)))))+e['suffix']):((isEq(e['ex'].car,getSymbol('*')))!=false?(e['prefix']+Apply(TopEnv.get('compile-append'),new Pair("1",new Pair("*",new Pair(e['ex'].cdr,new Pair(e['locs'],theNil)))))+e['suffix']):((isEq(e['ex'].car,getSymbol('-')))!=false?(e['prefix']+Apply(TopEnv.get('compile-minus'),new Pair("-",new Pair("-",new Pair(e['ex'].cdr,new Pair(e['locs'],theNil)))))+e['suffix']):((isEq(e['ex'].car,getSymbol('/')))!=false?(e['prefix']+Apply(TopEnv.get('compile-minus'),new Pair("1/",new Pair("/",new Pair(e['ex'].cdr,new Pair(e['locs'],theNil)))))+e['suffix']):((isEq(e['ex'].car,getSymbol('string-append')))!=false?(e['prefix']+Apply(TopEnv.get('compile-append'),new Pair("''",new Pair("+",new Pair(e['ex'].cdr,new Pair(e['locs'],theNil)))))+e['suffix']):((((isEq(e['ex'].car,getSymbol('eq?')))!=false?true:((isEq(e['ex'].car,getSymbol('=')))!=false?true:((isEq(e['ex'].car,getSymbol('eqv?')))!=false?true:((isEq(e['ex'].car,getSymbol('string=?')))!=false?true:isEq(e['ex'].car,getSymbol('char=?')))))))!=false?(e['prefix']+"isEq("+Apply(TopEnv.get('compile'),new Pair(e['ex'].cdr.car,new Pair(e['locs'],theNil)))+","+Apply(TopEnv.get('compile'),new Pair(e['ex'].cdr.cdr.car,new Pair(e['locs'],theNil)))+")"+e['suffix']):((isEq(e['ex'].car,getSymbol('list')))!=false?(e['prefix']+Apply(TopEnv.get('compile-list'),new Pair(e['ex'].cdr,new Pair(e['locs'],theNil)))+e['suffix']):((isEq(e['ex'].car,getSymbol('if')))!=false?(((e['ex'].cdr.cdr.cdr==theNil))!=false?TC(TopEnv.get('compile'),list=new Pair(e['ex'].cdr.cdr.car,new Pair(e['locs'],new Pair(e['tail'],new Pair((e['prefix']+"(("+Apply(TopEnv.get('compile'),new Pair(e['ex'].cdr.car,new Pair(e['locs'],theNil)))+")!=false?"),new Pair((":null)"+e['suffix']),theNil)))))):TC(TopEnv.get('compile'),list=new Pair(e['ex'].cdr.cdr.cdr.car,new Pair(e['locs'],new Pair(e['tail'],new Pair((e['prefix']+"(("+Apply(TopEnv.get('compile'),new Pair(e['ex'].cdr.car,new Pair(e['locs'],theNil)))+")!=false?"+Apply(TopEnv.get('compile'),new Pair(e['ex'].cdr.cdr.car,new Pair(e['locs'],new Pair(e['tail'],theNil))))+":"),new Pair((")"+e['suffix']),theNil))))))):((isEq(e['ex'].car,getSymbol('define-syntax')))!=false?(e['prefix']+"e['"+e['ex'].cdr.car.name+"']=new Syntax(e.get('"+e['ex'].cdr.cdr.car.car.name+"'),"+Apply(TopEnv.get('compile-quote'),new Pair(e['ex'].cdr.cdr.car.cdr,theNil))+")"+e['suffix']):((((isEq(e['ex'].car,getSymbol('define')))!=false?((e['ex'].cdr.car)instanceof Symbol):false))!=false?(((e['locs'])!=false?Apply(e['locs'],new Pair(getSymbol('add'),new Pair(e['ex'].cdr.car,theNil))):null),(e['prefix']+"e['"+e['ex'].cdr.car.name+"']="+Apply(TopEnv.get('compile'),new Pair(e['ex'].cdr.cdr.car,new Pair(e['locs'],theNil)))+e['suffix'])):((isEq(e['ex'].car,getSymbol('set!')))!=false?((((e['locs'])!=false?Apply(e['locs'],new Pair(getSymbol('memq'),new Pair(e['ex'].cdr.car,theNil))):false))!=false?TC(TopEnv.get('compile'),list=new Pair(e['ex'].cdr.cdr.car,new Pair(e['locs'],new Pair(false,new Pair((e['prefix']+"e['"+e['ex'].cdr.car.name+"']="),new Pair(e['suffix'],theNil)))))):TC(TopEnv.get('compile'),list=new Pair(e['ex'].cdr.cdr.car,new Pair(e['locs'],new Pair(false,new Pair((e['prefix']+"e.set('"+e['ex'].cdr.car.name+"',"),new Pair((")"+e['suffix']),theNil))))))):((isEq(e['ex'].car,getSymbol('lambda')))!=false?(e['prefix']+Apply(TopEnv.get('compile-lambda-obj'),new Pair(e['ex'].cdr.car,new Pair(e['ex'].cdr.cdr,new Pair(e['locs'],theNil))))+e['suffix']):((((isEq(e['ex'].car,getSymbol('define')))!=false?((e['ex'].cdr.car)instanceof Pair):false))!=false?(((e['locs'])!=false?Apply(e['locs'],new Pair(getSymbol('add'),new Pair(Apply(TopEnv.get('caadr'),new Pair(e['ex'],theNil)),theNil))):null),(e['prefix']+"e['"+Apply(TopEnv.get('caadr'),new Pair(e['ex'],theNil)).name+"']="+Apply(TopEnv.get('compile-lambda-obj'),new Pair(Apply(TopEnv.get('cdadr'),new Pair(e['ex'],theNil)),new Pair(e['ex'].cdr.cdr,new Pair(e['locs'],theNil))))+e['suffix'])):((isEq(e['ex'].car,getSymbol('apply')))!=false?(e['prefix']+e['app']+"("+Apply(TopEnv.get('compile'),new Pair(e['ex'].cdr.car,new Pair(e['locs'],theNil)))+","+((e['tail'])!=false?"list=":"")+Apply(TopEnv.get('compile-apply-list'),new Pair(e['ex'].cdr.cdr,new Pair(e['locs'],theNil)))+")"+e['suffix']):((((e['tail'])!=false?(((typeof(e['list-len'])=='number'))!=false?e['list-len']>=Apply(TopEnv.get('length'),new Pair(e['ex'].cdr,theNil)):false):false))!=false?(e['prefix']+"("+Apply(TopEnv.get('compile-reuse'),new Pair(e['ex'].cdr,new Pair("list",new Pair(e['locs'],theNil))))+","+"theTC.f="+Apply(TopEnv.get('compile'),new Pair(e['ex'].car,new Pair(e['locs'],theNil)))+",theTC.args=list,theTC)"+e['suffix']):TC(TopEnv.get('compile-list'),list=new Pair(e['ex'].cdr,new Pair(e['locs'],new Pair((e['prefix']+e['app']+"("+Apply(TopEnv.get('compile'),new Pair(e['ex'].car,new Pair(e['locs'],theNil)))+","+((e['tail'])!=false?"list=":"")),new Pair((")"+e['suffix']),theNil))))))))))))))))))))))))))))))))))))))))))))))))))));if(r!=theTC||r.f!=this)return r}});
e['compile-reuse']=new Lambda(new Pair(getSymbol('lst'),new Pair(getSymbol('var'),new Pair(getSymbol('locs'),theNil))),new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('pair?'),new Pair(getSymbol('lst'),theNil)),new Pair(new Pair(getSymbol('string-append'),new Pair("(",new Pair(getSymbol('var'),new Pair(".car=",new Pair(new Pair(getSymbol('compile'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('lst'),theNil)),new Pair(getSymbol('locs'),theNil))),new Pair("),",new Pair(new Pair(getSymbol('compile-reuse'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('lst'),theNil)),new Pair(new Pair(getSymbol('string-append'),new Pair(getSymbol('var'),new Pair(".cdr",theNil))),new Pair(getSymbol('locs'),theNil)))),theNil))))))),new Pair(new Pair(getSymbol('string-append'),new Pair("(",new Pair(getSymbol('var'),new Pair("=",new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('null?'),new Pair(getSymbol('lst'),theNil)),new Pair("theNil",new Pair(new Pair(getSymbol('compile'),new Pair(getSymbol('lst'),new Pair(getSymbol('locs'),theNil))),theNil)))),new Pair(")",theNil)))))),theNil)))),e,function(list){var r,e=new Env(this.env);while(true){e['lst']=list.car;e['var']=list.cdr.car;e['locs']=list.cdr.cdr.car;r=((((e['lst'])instanceof Pair))!=false?("("+e['var']+".car="+Apply(TopEnv.get('compile'),new Pair(e['lst'].car,new Pair(e['locs'],theNil)))+"),"+Apply(TopEnv.get('compile-reuse'),new Pair(e['lst'].cdr,new Pair((e['var']+".cdr"),new Pair(e['locs'],theNil))))):("("+e['var']+"="+(((e['lst']==theNil))!=false?"theNil":Apply(TopEnv.get('compile'),new Pair(e['lst'],new Pair(e['locs'],theNil))))+")"));if(r!=theTC||r.f!=this)return r}});
e['compile-predicate']=new Lambda(new Pair(getSymbol('op'),new Pair(getSymbol('lst'),new Pair(getSymbol('locs'),theNil))),new Pair(getSymbol('begin'),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('s'),new Pair(new Pair(getSymbol('string-append'),new Pair(new Pair(getSymbol('compile'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('lst'),theNil)),new Pair(getSymbol('locs'),theNil))),new Pair(getSymbol('op'),new Pair(new Pair(getSymbol('compile'),new Pair(new Pair(getSymbol('cadr'),new Pair(getSymbol('lst'),theNil)),new Pair(getSymbol('locs'),theNil))),theNil)))),theNil))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('null?'),new Pair(new Pair(getSymbol('cddr'),new Pair(getSymbol('lst'),theNil)),theNil)),new Pair(getSymbol('s'),new Pair(new Pair(getSymbol('string-append'),new Pair(getSymbol('s'),new Pair("&&",new Pair(new Pair(getSymbol('compile-predicate'),new Pair(getSymbol('op'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('lst'),theNil)),new Pair(getSymbol('locs'),theNil)))),theNil)))),theNil)))),theNil))),e,function(list){var r,e=new Env(this.env);while(true){e['op']=list.car;e['lst']=list.cdr.car;e['locs']=list.cdr.cdr.car;r=(e['s']=(Apply(TopEnv.get('compile'),new Pair(e['lst'].car,new Pair(e['locs'],theNil)))+e['op']+Apply(TopEnv.get('compile'),new Pair(e['lst'].cdr.car,new Pair(e['locs'],theNil)))),(((e['lst'].cdr.cdr==theNil))!=false?e['s']:(e['s']+"&&"+Apply(TopEnv.get('compile-predicate'),new Pair(e['op'],new Pair(e['lst'].cdr,new Pair(e['locs'],theNil)))))));if(r!=theTC||r.f!=this)return r}});
e['compile-minus']=new Lambda(new Pair(getSymbol('one'),new Pair(getSymbol('op'),new Pair(getSymbol('lst'),new Pair(getSymbol('locs'),theNil)))),new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('null?'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('lst'),theNil)),theNil)),new Pair(new Pair(getSymbol('string-append'),new Pair("(",new Pair(getSymbol('one'),new Pair(new Pair(getSymbol('compile'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('lst'),theNil)),new Pair(getSymbol('locs'),theNil))),new Pair(")",theNil))))),new Pair(new Pair(getSymbol('compile-append'),new Pair("0",new Pair(getSymbol('op'),new Pair(getSymbol('lst'),new Pair(getSymbol('locs'),theNil))))),theNil)))),e,function(list){var r,e=new Env(this.env);while(true){e['one']=list.car;e['op']=list.cdr.car;e['lst']=list.cdr.cdr.car;e['locs']=list.cdr.cdr.cdr.car;r=(((e['lst'].cdr==theNil))!=false?("("+e['one']+Apply(TopEnv.get('compile'),new Pair(e['lst'].car,new Pair(e['locs'],theNil)))+")"):TC(TopEnv.get('compile-append'),list=new Pair("0",new Pair(e['op'],new Pair(e['lst'],new Pair(e['locs'],theNil))))));if(r!=theTC||r.f!=this)return r}});
e['compile-append']=new Lambda(new Pair(getSymbol('zero'),new Pair(getSymbol('op'),new Pair(getSymbol('lst'),new Pair(getSymbol('locs'),getSymbol('q'))))),new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('null?'),new Pair(getSymbol('lst'),theNil)),new Pair(getSymbol('zero'),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('null?'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('lst'),theNil)),theNil)),new Pair(new Pair(getSymbol('compile'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('lst'),theNil)),new Pair(getSymbol('locs'),theNil))),new Pair(new Pair(getSymbol('string-append'),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('null?'),new Pair(getSymbol('q'),theNil)),new Pair("(",new Pair("",theNil)))),new Pair(new Pair(getSymbol('compile'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('lst'),theNil)),new Pair(getSymbol('locs'),theNil))),new Pair(getSymbol('op'),new Pair(new Pair(getSymbol('compile-append'),new Pair(getSymbol('zero'),new Pair(getSymbol('op'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('lst'),theNil)),new Pair(getSymbol('locs'),new Pair(true,theNil)))))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('null?'),new Pair(getSymbol('q'),theNil)),new Pair(")",new Pair("",theNil)))),theNil)))))),theNil)))),theNil)))),e,function(list){var r,e=new Env(this.env);while(true){e['zero']=list.car;e['op']=list.cdr.car;e['lst']=list.cdr.cdr.car;e['locs']=list.cdr.cdr.cdr.car;e['q']=list.cdr.cdr.cdr.cdr;r=(((e['lst']==theNil))!=false?e['zero']:(((e['lst'].cdr==theNil))!=false?TC(TopEnv.get('compile'),list=new Pair(e['lst'].car,new Pair(e['locs'],theNil))):((((e['q']==theNil))!=false?"(":"")+Apply(TopEnv.get('compile'),new Pair(e['lst'].car,new Pair(e['locs'],theNil)))+e['op']+Apply(TopEnv.get('compile-append'),new Pair(e['zero'],new Pair(e['op'],new Pair(e['lst'].cdr,new Pair(e['locs'],new Pair(true,theNil))))))+(((e['q']==theNil))!=false?")":""))));if(r!=theTC||r.f!=this)return r}});
e['compile-list']=new Lambda(new Pair(getSymbol('ex'),new Pair(getSymbol('locs'),getSymbol('tt'))),new Pair(getSymbol('begin'),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('prefix'),new Pair("",theNil))),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('suffix'),new Pair("",theNil))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('not'),new Pair(new Pair(getSymbol('null?'),new Pair(getSymbol('tt'),theNil)),theNil)),new Pair(new Pair(getSymbol('begin'),new Pair(new Pair(getSymbol('set!'),new Pair(getSymbol('prefix'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('tt'),theNil)),theNil))),new Pair(new Pair(getSymbol('set!'),new Pair(getSymbol('suffix'),new Pair(new Pair(getSymbol('cadr'),new Pair(getSymbol('tt'),theNil)),theNil))),theNil))),theNil))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('null?'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('string-append'),new Pair(getSymbol('prefix'),new Pair("theNil",new Pair(getSymbol('suffix'),theNil)))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('pair?'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('compile-list'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('ex'),theNil)),new Pair(getSymbol('locs'),new Pair(new Pair(getSymbol('string-append'),new Pair(getSymbol('prefix'),new Pair("new Pair(",new Pair(new Pair(getSymbol('compile'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),new Pair(getSymbol('locs'),theNil))),new Pair(",",theNil))))),new Pair(new Pair(getSymbol('string-append'),new Pair(")",new Pair(getSymbol('suffix'),theNil))),theNil))))),new Pair(new Pair(getSymbol('compile'),new Pair(getSymbol('ex'),new Pair(getSymbol('locs'),new Pair(false,new Pair(getSymbol('prefix'),new Pair(getSymbol('suffix'),theNil)))))),theNil)))),theNil)))),theNil))))),e,function(list){var r,e=new Env(this.env);while(true){e['ex']=list.car;e['locs']=list.cdr.car;e['tt']=list.cdr.cdr;r=(e['prefix']="",e['suffix']="",((((e['tt']==theNil)==false))!=false?(e['prefix']=e['tt'].car,e['suffix']=e['tt'].cdr.car):null),(((e['ex']==theNil))!=false?(e['prefix']+"theNil"+e['suffix']):((((e['ex'])instanceof Pair))!=false?TC(TopEnv.get('compile-list'),list=new Pair(e['ex'].cdr,new Pair(e['locs'],new Pair((e['prefix']+"new Pair("+Apply(TopEnv.get('compile'),new Pair(e['ex'].car,new Pair(e['locs'],theNil)))+","),new Pair((")"+e['suffix']),theNil))))):TC(TopEnv.get('compile'),list=new Pair(e['ex'],new Pair(e['locs'],new Pair(false,new Pair(e['prefix'],new Pair(e['suffix'],theNil)))))))));if(r!=theTC||r.f!=this)return r}});
e['compile-quote']=new Lambda(new Pair(getSymbol('ex'),getSymbol('tt')),new Pair(getSymbol('begin'),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('prefix'),new Pair("",theNil))),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('suffix'),new Pair("",theNil))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('not'),new Pair(new Pair(getSymbol('null?'),new Pair(getSymbol('tt'),theNil)),theNil)),new Pair(new Pair(getSymbol('begin'),new Pair(new Pair(getSymbol('set!'),new Pair(getSymbol('prefix'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('tt'),theNil)),theNil))),new Pair(new Pair(getSymbol('set!'),new Pair(getSymbol('suffix'),new Pair(new Pair(getSymbol('cadr'),new Pair(getSymbol('tt'),theNil)),theNil))),theNil))),theNil))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('null?'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('string-append'),new Pair(getSymbol('prefix'),new Pair("theNil",new Pair(getSymbol('suffix'),theNil)))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('symbol?'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('string-append'),new Pair(getSymbol('prefix'),new Pair("getSymbol('",new Pair(new Pair(getSymbol('symbol->string'),new Pair(getSymbol('ex'),theNil)),new Pair("')",new Pair(getSymbol('suffix'),theNil)))))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('pair?'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('compile-quote'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('string-append'),new Pair(getSymbol('prefix'),new Pair("new Pair(",new Pair(new Pair(getSymbol('compile-quote'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),theNil)),new Pair(",",theNil))))),new Pair(new Pair(getSymbol('string-append'),new Pair(")",new Pair(getSymbol('suffix'),theNil))),theNil)))),new Pair(new Pair(getSymbol('compile'),new Pair(getSymbol('ex'),new Pair(false,new Pair(false,new Pair(getSymbol('prefix'),new Pair(getSymbol('suffix'),theNil)))))),theNil)))),theNil)))),theNil)))),theNil))))),e,function(list){var r,e=new Env(this.env);while(true){e['ex']=list.car;e['tt']=list.cdr;r=(e['prefix']="",e['suffix']="",((((e['tt']==theNil)==false))!=false?(e['prefix']=e['tt'].car,e['suffix']=e['tt'].cdr.car):null),(((e['ex']==theNil))!=false?(e['prefix']+"theNil"+e['suffix']):((((e['ex'])instanceof Symbol))!=false?(e['prefix']+"getSymbol('"+e['ex'].name+"')"+e['suffix']):((((e['ex'])instanceof Pair))!=false?TC(TopEnv.get('compile-quote'),list=new Pair(e['ex'].cdr,new Pair((e['prefix']+"new Pair("+Apply(TopEnv.get('compile-quote'),new Pair(e['ex'].car,theNil))+","),new Pair((")"+e['suffix']),theNil)))):TC(TopEnv.get('compile'),list=new Pair(e['ex'],new Pair(false,new Pair(false,new Pair(e['prefix'],new Pair(e['suffix'],theNil))))))))));if(r!=theTC||r.f!=this)return r}});
e['compile-begin']=new Lambda(new Pair(getSymbol('ex'),new Pair(getSymbol('locs'),new Pair(getSymbol('tail'),new Pair(getSymbol('prefix'),new Pair(getSymbol('suffix'),getSymbol('q')))))),new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('null?'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('string-append'),new Pair(getSymbol('prefix'),new Pair("null",new Pair(getSymbol('suffix'),theNil)))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('null?'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('ex'),theNil)),theNil)),new Pair(new Pair(getSymbol('compile'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),new Pair(getSymbol('locs'),new Pair(getSymbol('tail'),new Pair(getSymbol('prefix'),new Pair(getSymbol('suffix'),theNil)))))),new Pair(new Pair(getSymbol('compile-begin'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('ex'),theNil)),new Pair(getSymbol('locs'),new Pair(getSymbol('tail'),new Pair(new Pair(getSymbol('string-append'),new Pair(getSymbol('prefix'),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('null?'),new Pair(getSymbol('q'),theNil)),new Pair("(",new Pair("",theNil)))),new Pair(new Pair(getSymbol('compile'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),new Pair(getSymbol('locs'),theNil))),new Pair(",",theNil))))),new Pair(new Pair(getSymbol('string-append'),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('null?'),new Pair(getSymbol('q'),theNil)),new Pair(")",new Pair("",theNil)))),new Pair(getSymbol('suffix'),theNil))),new Pair(true,theNil))))))),theNil)))),theNil)))),e,function(list){var r,e=new Env(this.env);while(true){e['ex']=list.car;e['locs']=list.cdr.car;e['tail']=list.cdr.cdr.car;e['prefix']=list.cdr.cdr.cdr.car;e['suffix']=list.cdr.cdr.cdr.cdr.car;e['q']=list.cdr.cdr.cdr.cdr.cdr;r=(((e['ex']==theNil))!=false?(e['prefix']+"null"+e['suffix']):(((e['ex'].cdr==theNil))!=false?TC(TopEnv.get('compile'),list=new Pair(e['ex'].car,new Pair(e['locs'],new Pair(e['tail'],new Pair(e['prefix'],new Pair(e['suffix'],theNil)))))):TC(TopEnv.get('compile-begin'),list=new Pair(e['ex'].cdr,new Pair(e['locs'],new Pair(e['tail'],new Pair((e['prefix']+(((e['q']==theNil))!=false?"(":"")+Apply(TopEnv.get('compile'),new Pair(e['ex'].car,new Pair(e['locs'],theNil)))+","),new Pair(((((e['q']==theNil))!=false?")":"")+e['suffix']),new Pair(true,theNil)))))))));if(r!=theTC||r.f!=this)return r}});
e['compile-apply-list']=new Lambda(new Pair(getSymbol('lst'),new Pair(getSymbol('locs'),theNil)),new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('null?'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('lst'),theNil)),theNil)),new Pair(new Pair(getSymbol('compile'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('lst'),theNil)),new Pair(getSymbol('locs'),new Pair(false,new Pair("",new Pair(".ListCopy()",theNil)))))),new Pair(new Pair(getSymbol('string-append'),new Pair("new Pair(",new Pair(new Pair(getSymbol('compile'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('lst'),theNil)),new Pair(getSymbol('locs'),theNil))),new Pair(",",new Pair(new Pair(getSymbol('compile-apply-list'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('lst'),theNil)),new Pair(getSymbol('locs'),theNil))),new Pair(")",theNil)))))),theNil)))),e,function(list){var r,e=new Env(this.env);while(true){e['lst']=list.car;e['locs']=list.cdr.car;r=(((e['lst'].cdr==theNil))!=false?TC(TopEnv.get('compile'),list=new Pair(e['lst'].car,new Pair(e['locs'],new Pair(false,new Pair("",new Pair(".ListCopy()",theNil)))))):("new Pair("+Apply(TopEnv.get('compile'),new Pair(e['lst'].car,new Pair(e['locs'],theNil)))+","+Apply(TopEnv.get('compile-apply-list'),new Pair(e['lst'].cdr,new Pair(e['locs'],theNil)))+")"));if(r!=theTC||r.f!=this)return r}});
e['compile-lambda-args']=new Lambda(new Pair(getSymbol('args'),new Pair(getSymbol('var'),theNil)),new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('null?'),new Pair(getSymbol('args'),theNil)),new Pair("",new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('symbol?'),new Pair(getSymbol('args'),theNil)),new Pair(new Pair(getSymbol('string-append'),new Pair("e['",new Pair(new Pair(getSymbol('symbol->string'),new Pair(getSymbol('args'),theNil)),new Pair("']=",new Pair(getSymbol('var'),new Pair(";",theNil)))))),new Pair(new Pair(getSymbol('string-append'),new Pair("e['",new Pair(new Pair(getSymbol('symbol->string'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('args'),theNil)),theNil)),new Pair("']=",new Pair(getSymbol('var'),new Pair(".car;",new Pair(new Pair(getSymbol('compile-lambda-args'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('args'),theNil)),new Pair(new Pair(getSymbol('string-append'),new Pair(getSymbol('var'),new Pair(".cdr",theNil))),theNil))),theNil))))))),theNil)))),theNil)))),e,function(list){var r,e=new Env(this.env);while(true){e['args']=list.car;e['var']=list.cdr.car;r=(((e['args']==theNil))!=false?"":((((e['args'])instanceof Symbol))!=false?("e['"+e['args'].name+"']="+e['var']+";"):("e['"+e['args'].car.name+"']="+e['var']+".car;"+Apply(TopEnv.get('compile-lambda-args'),new Pair(e['args'].cdr,new Pair((e['var']+".cdr"),theNil))))));if(r!=theTC||r.f!=this)return r}});
e['compile-extract-children']=new Lambda(new Pair(getSymbol('obj'),getSymbol('c')),new Pair(getSymbol('begin'),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('tmp-name'),new Pair(false,theNil))),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('a'),new Pair(false,theNil))),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('d'),new Pair(false,theNil))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('pair?'),new Pair(getSymbol('obj'),theNil)),new Pair(new Pair(getSymbol('not'),new Pair(new Pair(getSymbol('eq?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('obj'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('quote'),theNil)),theNil))),theNil)),new Pair(false,theNil)))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eq?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('obj'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('lambda'),theNil)),theNil))),new Pair(new Pair(getSymbol('begin'),new Pair(new Pair(getSymbol('set!'),new Pair(getSymbol('tmp-name'),new Pair(new Pair(getSymbol('gen-sym'),theNil),theNil))),new Pair(new Pair(getSymbol('cons'),new Pair(new Pair(getSymbol('list'),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('clone'),theNil)),new Pair(getSymbol('tmp-name'),theNil))),new Pair(new Pair(getSymbol('cons'),new Pair(new Pair(getSymbol('cons'),new Pair(getSymbol('tmp-name'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('obj'),theNil)),theNil))),new Pair(getSymbol('c'),theNil))),theNil))),theNil))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eq?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('obj'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('define'),theNil)),theNil))),new Pair(new Pair(getSymbol('pair?'),new Pair(new Pair(getSymbol('cadr'),new Pair(getSymbol('obj'),theNil)),theNil)),new Pair(false,theNil)))),new Pair(new Pair(getSymbol('begin'),new Pair(new Pair(getSymbol('set!'),new Pair(getSymbol('tmp-name'),new Pair(new Pair(getSymbol('gen-sym'),theNil),theNil))),new Pair(new Pair(getSymbol('cons'),new Pair(new Pair(getSymbol('list'),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('define'),theNil)),new Pair(new Pair(getSymbol('caadr'),new Pair(getSymbol('obj'),theNil)),new Pair(new Pair(getSymbol('list'),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('clone'),theNil)),new Pair(getSymbol('tmp-name'),theNil))),theNil)))),new Pair(new Pair(getSymbol('cons'),new Pair(new Pair(getSymbol('cons'),new Pair(getSymbol('tmp-name'),new Pair(new Pair(getSymbol('cons'),new Pair(new Pair(getSymbol('cdadr'),new Pair(getSymbol('obj'),theNil)),new Pair(new Pair(getSymbol('cddr'),new Pair(getSymbol('obj'),theNil)),theNil))),theNil))),new Pair(getSymbol('c'),theNil))),theNil))),theNil))),new Pair(new Pair(getSymbol('begin'),new Pair(new Pair(getSymbol('set!'),new Pair(getSymbol('a'),new Pair(new Pair(getSymbol('compile-extract-children'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('obj'),theNil)),theNil)),theNil))),new Pair(new Pair(getSymbol('set!'),new Pair(getSymbol('d'),new Pair(new Pair(getSymbol('compile-extract-children'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('obj'),theNil)),theNil)),theNil))),new Pair(new Pair(getSymbol('cons'),new Pair(new Pair(getSymbol('cons'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('a'),theNil)),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('d'),theNil)),theNil))),new Pair(new Pair(getSymbol('append'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('a'),theNil)),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('d'),theNil)),theNil))),theNil))),theNil)))),theNil)))),theNil)))),new Pair(new Pair(getSymbol('cons'),new Pair(getSymbol('obj'),new Pair(getSymbol('c'),theNil))),theNil)))),theNil))))),e,function(list){var r,e=new Env(this.env);while(true){e['obj']=list.car;e['c']=list.cdr;r=(e['tmp-name']=false,e['a']=false,e['d']=false,((((((e['obj'])instanceof Pair))!=false?(isEq(e['obj'].car,getSymbol('quote'))==false):false))!=false?((isEq(e['obj'].car,getSymbol('lambda')))!=false?(e['tmp-name']=Apply(TopEnv.get('gen-sym'),theNil),new Pair(new Pair(getSymbol('clone'),new Pair(e['tmp-name'],theNil)),new Pair(new Pair(e['tmp-name'],e['obj'].cdr),e['c']))):((((isEq(e['obj'].car,getSymbol('define')))!=false?((e['obj'].cdr.car)instanceof Pair):false))!=false?(e['tmp-name']=Apply(TopEnv.get('gen-sym'),theNil),new Pair(new Pair(getSymbol('define'),new Pair(Apply(TopEnv.get('caadr'),new Pair(e['obj'],theNil)),new Pair(new Pair(getSymbol('clone'),new Pair(e['tmp-name'],theNil)),theNil))),new Pair(new Pair(e['tmp-name'],new Pair(Apply(TopEnv.get('cdadr'),new Pair(e['obj'],theNil)),e['obj'].cdr.cdr)),e['c']))):(e['a']=Apply(TopEnv.get('compile-extract-children'),new Pair(e['obj'].car,theNil)),e['d']=Apply(TopEnv.get('compile-extract-children'),new Pair(e['obj'].cdr,theNil)),new Pair(new Pair(e['a'].car,e['d'].car),Apply(TopEnv.get('append'),new Pair(e['a'].cdr,new Pair(e['d'].cdr,theNil))))))):new Pair(e['obj'],e['c'])));if(r!=theTC||r.f!=this)return r}});
e['compile-lambda-obj']=new Lambda(new Pair(getSymbol('args'),new Pair(getSymbol('body'),getSymbol('tt'))),new Pair(getSymbol('begin'),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('parent-locs'),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('null?'),new Pair(getSymbol('tt'),theNil)),new Pair(false,new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('tt'),theNil)),theNil)))),theNil))),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('ex'),new Pair(new Pair(getSymbol('compile-extract-children'),new Pair(getSymbol('body'),theNil)),theNil))),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('ll'),new Pair(false,theNil))),new Pair(new Pair(getSymbol('set!'),new Pair(getSymbol('body'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),theNil))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('not'),new Pair(new Pair(getSymbol('null?'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('ex'),theNil)),theNil)),theNil)),new Pair(new Pair(getSymbol('set!'),new Pair(getSymbol('parent-locs'),new Pair(new Pair(getSymbol('compile-make-locals'),new Pair(new Pair(getSymbol('map+'),new Pair(getSymbol('car'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('ex'),theNil)),theNil))),new Pair(getSymbol('parent-locs'),theNil))),theNil))),theNil))),new Pair(new Pair(getSymbol('set!'),new Pair(getSymbol('parent-locs'),new Pair(new Pair(getSymbol('compile-make-locals'),new Pair(getSymbol('args'),new Pair(getSymbol('parent-locs'),theNil))),theNil))),new Pair(new Pair(getSymbol('set!'),new Pair(getSymbol('ll'),new Pair(new Pair(getSymbol('compile-lambda'),new Pair(getSymbol('args'),new Pair(getSymbol('body'),new Pair(getSymbol('parent-locs'),theNil)))),theNil))),new Pair(new Pair(getSymbol('string-append'),new Pair("new Lambda(",new Pair(new Pair(getSymbol('compile-quote'),new Pair(getSymbol('args'),theNil)),new Pair(",",new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('null?'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('body'),theNil)),theNil)),new Pair(new Pair(getSymbol('compile-quote'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('body'),theNil)),theNil)),new Pair(new Pair(getSymbol('compile-quote'),new Pair(new Pair(getSymbol('cons'),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('begin'),theNil)),new Pair(getSymbol('body'),theNil))),theNil)),theNil)))),new Pair(",",new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('null?'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('ex'),theNil)),theNil)),new Pair("e",new Pair(new Pair(getSymbol('apply'),new Pair(getSymbol('string-append'),new Pair("new Env(e)",new Pair(new Pair(getSymbol('map+'),new Pair(new Pair(getSymbol('clone'),new Pair(getSymbol('_52_'),theNil)),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('ex'),theNil)),theNil))),theNil)))),theNil)))),new Pair(",",new Pair(getSymbol('ll'),new Pair(")",theNil)))))))))),theNil))))))))),new Env(e).With('_52_',new Lambda(new Pair(getSymbol('l'),theNil),new Pair(getSymbol('string-append'),new Pair(".With('",new Pair(new Pair(getSymbol('symbol->string'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('l'),theNil)),theNil)),new Pair("',",new Pair(new Pair(getSymbol('compile-lambda-obj'),new Pair(new Pair(getSymbol('cadr'),new Pair(getSymbol('l'),theNil)),new Pair(new Pair(getSymbol('cddr'),new Pair(getSymbol('l'),theNil)),new Pair(getSymbol('parent-locs'),theNil)))),new Pair(")",theNil)))))),e,function(list){var r,e=new Env(this.env);while(true){e['l']=list.car;r=(".With('"+e['l'].car.name+"',"+Apply(TopEnv.get('compile-lambda-obj'),new Pair(e['l'].cdr.car,new Pair(e['l'].cdr.cdr,new Pair(e.parentEnv['parent-locs'],theNil))))+")");if(r!=theTC||r.f!=this)return r}})),function(list){var r,e=new Env(this.env);while(true){e['args']=list.car;e['body']=list.cdr.car;e['tt']=list.cdr.cdr;r=(e['parent-locs']=(((e['tt']==theNil))!=false?false:e['tt'].car),e['ex']=Apply(TopEnv.get('compile-extract-children'),new Pair(e['body'],theNil)),e['ll']=false,e['body']=e['ex'].car,((((e['ex'].cdr==theNil)==false))!=false?e['parent-locs']=Apply(TopEnv.get('compile-make-locals'),new Pair(Apply(TopEnv.get('map+'),new Pair(TopEnv.get('car'),new Pair(e['ex'].cdr,theNil))),new Pair(e['parent-locs'],theNil))):null),e['parent-locs']=Apply(TopEnv.get('compile-make-locals'),new Pair(e['args'],new Pair(e['parent-locs'],theNil))),e['ll']=Apply(TopEnv.get('compile-lambda'),new Pair(e['args'],new Pair(e['body'],new Pair(e['parent-locs'],theNil)))),("new Lambda("+Apply(TopEnv.get('compile-quote'),new Pair(e['args'],theNil))+","+(((e['body'].cdr==theNil))!=false?Apply(TopEnv.get('compile-quote'),new Pair(e['body'].car,theNil)):Apply(TopEnv.get('compile-quote'),new Pair(new Pair(getSymbol('begin'),e['body']),theNil)))+","+(((e['ex'].cdr==theNil))!=false?"e":Apply(TopEnv.get('string-append'),new Pair("new Env(e)",Apply(TopEnv.get('map+'),new Pair(e.parentEnv['_52_'].clone(e),new Pair(e['ex'].cdr,theNil))).ListCopy())))+","+e['ll']+")"));if(r!=theTC||r.f!=this)return r}});
e['compile-make-locals']=new Lambda(new Pair(getSymbol('lst'),new Pair(getSymbol('parent'),theNil)),new Pair(getSymbol('clone'),new Pair(getSymbol('_53_'),theNil)),new Env(e).With('_53_',new Lambda(new Pair(getSymbol('msg'),new Pair(getSymbol('v'),getSymbol('tt'))),new Pair(getSymbol('begin'),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('e'),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('null?'),new Pair(getSymbol('tt'),theNil)),new Pair("e",new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('tt'),theNil)),theNil)))),theNil))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eq?'),new Pair(getSymbol('msg'),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('set!'),theNil)),theNil))),new Pair(new Pair(getSymbol('set!'),new Pair(getSymbol('lst'),new Pair(getSymbol('v'),theNil))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eq?'),new Pair(getSymbol('msg'),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('get'),theNil)),theNil))),new Pair(getSymbol('lst'),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eq?'),new Pair(getSymbol('msg'),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('add'),theNil)),theNil))),new Pair(new Pair(getSymbol('set!'),new Pair(getSymbol('lst'),new Pair(new Pair(getSymbol('cons'),new Pair(getSymbol('v'),new Pair(getSymbol('lst'),theNil))),theNil))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eq?'),new Pair(getSymbol('msg'),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('memq'),theNil)),theNil))),new Pair(new Pair(getSymbol('memq'),new Pair(getSymbol('v'),new Pair(getSymbol('lst'),theNil))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eq?'),new Pair(getSymbol('msg'),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('gen'),theNil)),theNil))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('memq'),new Pair(getSymbol('v'),new Pair(getSymbol('lst'),theNil))),new Pair(new Pair(getSymbol('string-append'),new Pair(getSymbol('e'),new Pair("['",new Pair(new Pair(getSymbol('symbol->string'),new Pair(getSymbol('v'),theNil)),new Pair("']",theNil))))),new Pair(new Pair(getSymbol('if'),new Pair(getSymbol('parent'),new Pair(new Pair(getSymbol('parent'),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('gen'),theNil)),new Pair(getSymbol('v'),new Pair(new Pair(getSymbol('string-append'),new Pair(getSymbol('e'),new Pair(".parentEnv",theNil))),theNil)))),new Pair(new Pair(getSymbol('string-append'),new Pair("TopEnv.get('",new Pair(new Pair(getSymbol('symbol->string'),new Pair(getSymbol('v'),theNil)),new Pair("')",theNil)))),theNil)))),theNil)))),theNil))),theNil)))),theNil)))),theNil)))),theNil)))),theNil))),e,function(list){var r,e=new Env(this.env);while(true){e['msg']=list.car;e['v']=list.cdr.car;e['tt']=list.cdr.cdr;r=(e['e']=(((e['tt']==theNil))!=false?"e":e['tt'].car),((isEq(e['msg'],getSymbol('set!')))!=false?e.set('lst',e['v']):((isEq(e['msg'],getSymbol('get')))!=false?e.parentEnv['lst']:((isEq(e['msg'],getSymbol('add')))!=false?e.set('lst',new Pair(e['v'],e.parentEnv['lst'])):((isEq(e['msg'],getSymbol('memq')))!=false?TC(TopEnv.get('memq'),list=new Pair(e['v'],new Pair(e.parentEnv['lst'],theNil))):((isEq(e['msg'],getSymbol('gen')))!=false?((Apply(TopEnv.get('memq'),new Pair(e['v'],new Pair(e.parentEnv['lst'],theNil))))!=false?(e['e']+"['"+e['v'].name+"']"):((e.parentEnv['parent'])!=false?TC(e.parentEnv['parent'],list=new Pair(getSymbol('gen'),new Pair(e['v'],new Pair((e['e']+".parentEnv"),theNil)))):("TopEnv.get('"+e['v'].name+"')"))):null))))));if(r!=theTC||r.f!=this)return r}})),function(list){var r,e=new Env(this.env);while(true){e['lst']=list.car;e['parent']=list.cdr.car;r=e.parentEnv['_53_'].clone(e);if(r!=theTC||r.f!=this)return r}});
e['compile-lambda']=new Lambda(new Pair(getSymbol('args'),new Pair(getSymbol('body'),new Pair(getSymbol('locs'),theNil))),new Pair(getSymbol('compile-begin'),new Pair(getSymbol('body'),new Pair(getSymbol('locs'),new Pair(true,new Pair(new Pair(getSymbol('string-append'),new Pair("function(list){var r,e=new Env(this.env);while(true){",new Pair(new Pair(getSymbol('compile-lambda-args'),new Pair(getSymbol('args'),new Pair("list",theNil))),new Pair("r=",theNil)))),new Pair(new Pair(getSymbol('string-append'),new Pair(";if(r!=theTC||r.f!=this)return r}}",theNil)),theNil)))))),e,function(list){var r,e=new Env(this.env);while(true){e['args']=list.car;e['body']=list.cdr.car;e['locs']=list.cdr.cdr.car;r=TC(TopEnv.get('compile-begin'),list=new Pair(e['body'],new Pair(e['locs'],new Pair(true,new Pair(("function(list){var r,e=new Env(this.env);while(true){"+Apply(TopEnv.get('compile-lambda-args'),new Pair(e['args'],new Pair("list",theNil)))+"r="),new Pair(";if(r!=theTC||r.f!=this)return r}}",theNil))))));if(r!=theTC||r.f!=this)return r}});
e['eval-compiled']=new Lambda(new Pair(getSymbol('s'),theNil),new Pair(getSymbol('js-eval'),new Pair(new Pair(getSymbol('string-append'),new Pair("var e=TopEnv;",new Pair(getSymbol('s'),theNil))),theNil)),e,function(list){var r,e=new Env(this.env);while(true){e['s']=list.car;r=TC(TopEnv.get('js-eval'),list=new Pair(("var e=TopEnv;"+e['s']),theNil));if(r!=theTC||r.f!=this)return r}});
e['compiled']=new Lambda(new Pair(getSymbol('s'),theNil),new Pair(getSymbol('js-invoke'),new Pair(new Pair(getSymbol('get-prop'),new Pair(getSymbol('s'),new Pair("compiled",theNil))),new Pair("toString",theNil))),e,function(list){var r,e=new Env(this.env);while(true){e['s']=list.car;r=TC(TopEnv.get('js-invoke'),list=new Pair(e['s']["compiled"],new Pair("toString",theNil)));if(r!=theTC||r.f!=this)return r}});
e['compile-lib']=new Lambda(theNil,new Pair(getSymbol('begin'),new Pair(new Pair(getSymbol('js-eval'),new Pair("document.getElementById('jit').checked=true",theNil)),new Pair(new Pair(getSymbol('js-eval'),new Pair("document.getElementById('echoInp').checked=false",theNil)),new Pair(new Pair(getSymbol('js-eval'),new Pair("document.getElementById('echoRes').checked=false",theNil)),new Pair(new Pair(getSymbol('js-eval'),new Pair("document.getElementById('log').value=''",theNil)),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('lib'),new Pair(new Pair(getSymbol('parse'),new Pair(new Pair(getSymbol('js-eval'),new Pair("document.getElementById('lib').innerHTML",theNil)),theNil)),theNil))),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('print'),new Pair(new Pair(getSymbol('clone'),new Pair(getSymbol('_54_'),theNil)),theNil))),new Pair(new Pair(getSymbol('print'),new Pair("var e=TopEnv",theNil)),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('print-compiled'),new Pair(new Pair(getSymbol('clone'),new Pair(getSymbol('_55_'),theNil)),theNil))),new Pair(new Pair(getSymbol('for-each'),new Pair(getSymbol('print-compiled'),new Pair(getSymbol('lib'),theNil))),theNil)))))))))),new Env(e).With('_54_',new Lambda(new Pair(getSymbol('x'),theNil),new Pair(getSymbol('begin'),new Pair(new Pair(getSymbol('display'),new Pair(getSymbol('x'),theNil)),new Pair(new Pair(getSymbol('display'),new Pair(getChar(';'),theNil)),new Pair(new Pair(getSymbol('newline'),theNil),theNil)))),e,function(list){var r,e=new Env(this.env);while(true){e['x']=list.car;r=(Apply(TopEnv.get('display'),new Pair(e['x'],theNil)),Apply(TopEnv.get('display'),new Pair(getChar(';'),theNil)),TC(TopEnv.get('newline'),list=theNil));if(r!=theTC||r.f!=this)return r}})).With('_55_',new Lambda(new Pair(getSymbol('x'),theNil),new Pair(getSymbol('print'),new Pair(new Pair(getSymbol('compile'),new Pair(getSymbol('x'),theNil)),theNil)),e,function(list){var r,e=new Env(this.env);while(true){e['x']=list.car;r=TC(e.parentEnv['print'],list=new Pair(Apply(TopEnv.get('compile'),new Pair(e['x'],theNil)),theNil));if(r!=theTC||r.f!=this)return r}})),function(list){var r,e=new Env(this.env);while(true){r=(Apply(TopEnv.get('js-eval'),new Pair("document.getElementById('jit').checked=true",theNil)),Apply(TopEnv.get('js-eval'),new Pair("document.getElementById('echoInp').checked=false",theNil)),Apply(TopEnv.get('js-eval'),new Pair("document.getElementById('echoRes').checked=false",theNil)),Apply(TopEnv.get('js-eval'),new Pair("document.getElementById('log').value=''",theNil)),e['lib']=Apply(TopEnv.get('parse'),new Pair(Apply(TopEnv.get('js-eval'),new Pair("document.getElementById('lib').innerHTML",theNil)),theNil)),e['print']=e.parentEnv['_54_'].clone(e),Apply(e['print'],new Pair("var e=TopEnv",theNil)),e['print-compiled']=e.parentEnv['_55_'].clone(e),TC(TopEnv.get('for-each'),list=new Pair(e['print-compiled'],new Pair(e['lib'],theNil))));if(r!=theTC||r.f!=this)return r}});
e['server']=new Lambda(new Pair(getSymbol('x'),theNil),new Pair(getSymbol('js-invoke'),new Pair(new Pair(getSymbol('js-eval'),new Pair("window.frames.hf",theNil)),new Pair("navigate",new Pair(new Pair(getSymbol('string-append'),new Pair("servlet/db?s=",new Pair(new Pair(getSymbol('encode'),new Pair(new Pair(getSymbol('str'),new Pair(getSymbol('x'),theNil)),theNil)),theNil))),theNil)))),e,function(list){var r,e=new Env(this.env);while(true){e['x']=list.car;r=TC(TopEnv.get('js-invoke'),list=new Pair(Apply(TopEnv.get('js-eval'),new Pair("window.frames.hf",theNil)),new Pair("navigate",new Pair(("servlet/db?s="+Apply(TopEnv.get('encode'),new Pair(Str(e['x']),theNil))),theNil))));if(r!=theTC||r.f!=this)return r}});
e['transform']=new Lambda(new Pair(getSymbol('ex'),theNil),new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('pair?'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('symbol?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),theNil)),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eq?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('quote'),theNil)),theNil))),new Pair(getSymbol('ex'),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eq?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('begin'),theNil)),theNil))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('null?'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('ex'),theNil)),theNil)),new Pair(false,new Pair(new Pair(getSymbol('null?'),new Pair(new Pair(getSymbol('cddr'),new Pair(getSymbol('ex'),theNil)),theNil)),theNil)))),new Pair(false,theNil)))),new Pair(new Pair(getSymbol('transform'),new Pair(new Pair(getSymbol('cadr'),new Pair(getSymbol('ex'),theNil)),theNil)),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eq?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('lambda'),theNil)),theNil))),new Pair(true,new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('eq?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('define'),theNil)),theNil))),new Pair(true,new Pair(new Pair(getSymbol('eq?'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('quote'),new Pair(getSymbol('set!'),theNil)),theNil))),theNil)))),theNil)))),new Pair(new Pair(getSymbol('cons'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('cons'),new Pair(new Pair(getSymbol('cadr'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('map+'),new Pair(getSymbol('transform'),new Pair(new Pair(getSymbol('cddr'),new Pair(getSymbol('ex'),theNil)),theNil))),theNil))),theNil))),new Pair(new Pair(getSymbol('begin'),new Pair(new Pair(getSymbol('define'),new Pair(getSymbol('x'),new Pair(new Pair(getSymbol('eval'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),theNil)),theNil))),new Pair(new Pair(getSymbol('if'),new Pair(new Pair(getSymbol('syntax?'),new Pair(getSymbol('x'),theNil)),new Pair(new Pair(getSymbol('transform'),new Pair(new Pair(getSymbol('apply'),new Pair(new Pair(getSymbol('get-prop'),new Pair(getSymbol('x'),new Pair("transformer",theNil))),new Pair(getSymbol('ex'),new Pair(new Pair(getSymbol('get-prop'),new Pair(getSymbol('x'),new Pair("args",theNil))),theNil)))),theNil)),new Pair(new Pair(getSymbol('cons'),new Pair(new Pair(getSymbol('car'),new Pair(getSymbol('ex'),theNil)),new Pair(new Pair(getSymbol('map+'),new Pair(getSymbol('transform'),new Pair(new Pair(getSymbol('cdr'),new Pair(getSymbol('ex'),theNil)),theNil))),theNil))),theNil)))),theNil))),theNil)))),theNil)))),theNil)))),new Pair(new Pair(getSymbol('map+'),new Pair(getSymbol('transform'),new Pair(getSymbol('ex'),theNil))),theNil)))),new Pair(getSymbol('ex'),theNil)))),e,function(list){var r,e=new Env(this.env);while(true){e['ex']=list.car;r=((((e['ex'])instanceof Pair))!=false?((((e['ex'].car)instanceof Symbol))!=false?((isEq(e['ex'].car,getSymbol('quote')))!=false?e['ex']:((((isEq(e['ex'].car,getSymbol('begin')))!=false?(((e['ex'].cdr==theNil))!=false?false:(e['ex'].cdr.cdr==theNil)):false))!=false?TC(TopEnv.get('transform'),list=new Pair(e['ex'].cdr.car,theNil)):((((isEq(e['ex'].car,getSymbol('lambda')))!=false?true:((isEq(e['ex'].car,getSymbol('define')))!=false?true:isEq(e['ex'].car,getSymbol('set!')))))!=false?new Pair(e['ex'].car,new Pair(e['ex'].cdr.car,Apply(TopEnv.get('map+'),new Pair(TopEnv.get('transform'),new Pair(e['ex'].cdr.cdr,theNil))))):(e['x']=Apply(TopEnv.get('eval'),new Pair(e['ex'].car,theNil)),((((e['x'])instanceof Syntax))!=false?TC(TopEnv.get('transform'),list=new Pair(Apply(e['x']["transformer"],new Pair(e['ex'],e['x']["args"].ListCopy())),theNil)):new Pair(e['ex'].car,Apply(TopEnv.get('map+'),new Pair(TopEnv.get('transform'),new Pair(e['ex'].cdr,theNil))))))))):TC(TopEnv.get('map+'),list=new Pair(TopEnv.get('transform'),new Pair(e['ex'],theNil)))):e['ex']);if(r!=theTC||r.f!=this)return r}});

// added by MH on 14/6/08
e['true'] = true;
e['false'] = false;

// Library end

  ShowEnv = TopEnv = new Env(TopEnv);
  //  showSymbols();
}

//
// Compiler...
//

var theCannot = new Ex("Lambda cannot be compiled")

function Apply(f,args) {

Again: while(true) {

  if( f instanceof Lambda ) {

    if( f.compiled == undefined ) {

     // var jitComp = TopEnv.get('compile-lambda');
      try {
        var jitComp = TopEnv.get('compile-lambda-obj');
      } catch( ee ) { throw theCannot }

      f.compiled = false;
      var expr = new Pair(jitComp,
                 new Pair(new Pair(theQuote,new Pair(f.args,theNil)),
                 new Pair(new Pair(theQuote,new Pair(
                          new Pair(f.body,theNil),theNil)),
                 theNil)));
      try {
        var res = doEval(expr,true);
       // f.compiled = eval("var tmp="+res+";tmp");
        e = f.env; eval("tmp="+res);
        f.compiled = tmp.compiled;
       // Rebuild lambda to change local (lambda())s to (clone)s
        f.body = tmp.body;
        f.env = tmp.env;
      } catch( ex ) { throw ex;
      }
    }
    if( f.compiled == false ) {
     // Back to interpretation...
      try {
        var state = new State(null,null,topCC);
        state.obj = callF(f,args,state);
        while( true ) {
          if( state.Eval(true) ) {
            state.ready = false;
            state.cont();
          }
        }
     // throw theCannot;
      } catch(ex) {
        if( ex instanceof Ex )
          return ex;
        else if( ex instanceof State )
          return ex.obj;
        else
          throw new Ex(ex.description); // throw ex;
      }
    }

    var res = f.compiled(args);
    if( res == theTC ) {
      f = res.f; args = res.args;
      continue Again;
    }
    return res;

  } else if( f instanceof Function ) {

    if( f.FType == undefined ) {
      if( /^\s*function\s*\(\s*(list|)\s*\)/.exec(f) ) f.FType=1;
     // else if( /^\s*function\s*\(list,env\)/.exec(f) ) f.FType=2;
      else f.FType=3;
    }

    if( f.FType == 1 ) return f(args);
/*
    if( f.FType == 2 ) {
      var res = f(args);
      if( res == theTC ) {
        f = res.f; args = res.args;
        continue Again;
      }
      return res;
    }
*/
    throw new Ex("JIT: Apply to invalid function, maybe call/cc");

  } else if( f instanceof Continuation ) {
    throw new State(args,null,f); // Give it to the interpreter
  } else throw new Ex("JIT: Apply to "+Str(f));
}}

// Tail-Calls

function TC(f,args) {
  theTC.f=f; theTC.args=args;
  return theTC;
}

var theTC = new Object();

//
// Interface things...
//

var buf1='';

function key1(srcElement) {
  buf1 = srcElement.value;
}

function key2(srcElement) {
  var buf2 = srcElement.value;
  var re = /(\n|\r\n){2}$/;
  if( !re.test(buf1) && re.test(buf2) ) {
    clickEval(); buf1 = buf2;
  }
}

function checkEdit(srcElement) {
  var e = srcElement, p = new Parser(e.value);
  var o = p.getObject();
  if( o instanceof Pair ) {
    e.parentElement.innerHTML = o.Html();
  }
  while( (m = p.getObject()) != null ) {
    var td = e.parentElement,
        tr = td.parentElement,
        tb = tr.parentElement,
        r0 = tb.rows[0];
    if( tb.rows.length == 1 ) { // horizontal
      var cell = tr.insertCell(td.cellIndex+1);
    } else if( r0.cells.length == 3 ) { // vertical
      r0.cells[0].rowSpan++;
      r0.cells[2].rowSpan++;
      var row = tb.insertRow(tr.rowIndex+1),
          cell = row.insertCell(0);
    } else {
      alert('Error!'); return;
    }
    cell.innerHTML = m.Html();
    cell.onclick = editCell;
    e.value = o.Str();
  }
}

function editCell(event) {
  var i, o = event.srcElement;
  if( o.children.length == 0 && // 2Do: merge subtrees...
      ! /^(\(|\)|)$/.test( o.innerHTML ) ) {
    var inp = document.createElement('input');
    inp.value = o.innerHTML;
    inp.onkeyup = function() { checkEdit(inp) };
    o.innerHTML = '';
    o.appendChild(inp);
    inp.focus();
  }
}

function hv(o) {
  var tr = o.parentElement, tbody = tr.parentElement;

  var isH = tbody.rows.length == 1 && tr.cells.length > 3;
  var isV = tbody.rows.length > 1 && tr.cells.length == 3;
  var isT = tbody.rows.length > 1 && tr.cells.length == 4;

  // 2Do: insert cell - esp. in (), move up/down, etc.

  if( isH /*tr.cells.length > 3*/ ) {
    tr.cells[0].rowSpan = tr.cells.length - 2;
    tr.cells[tr.cells.length-1].rowSpan = tr.cells.length - 2;
    //
    while( tr.cells.length > 3) {
      var cell = tr.cells[2];
/*
      tbody.insertRow().insertCell().innerHTML = cell.innerHTML;
      tr.deleteCell(2);
*/
      tr.removeChild(cell);
      tbody.insertRow().appendChild(cell);
    }
  } else if( isV ) {
    while( tbody.rows.length > 1 ) {
      var cell = tbody.rows[1].cells[0];
/*
      tr.insertCell(tr.cells.length-1).innerHTML = cell.innerHTML;
*/
      tr.insertBefore(cell,tr.cells[tr.cells.length-1]);
      tbody.deleteRow(1);
    }
  }
}

function objType(o) {
  if( isNil(o) ) return 'null';
  if( o instanceof Lambda ) return 'lambda';
  if( o instanceof Pair ) return 'list';
  if( o instanceof Char ) return 'char';
  if( o instanceof Array ) return 'vector';
  if( o instanceof Symbol ) return 'symbol';
  if( o instanceof Continuation ) return 'continuation';
  if( o instanceof Syntax ) return 'syntax';
  return typeof(o);
}

;
var f = [[0,0],[1,0],[0,1]];
//var p = make_painter_from_url("http://whatisaymatters.com/adam/PNG_Cartoons/CAT.png");
//p(f);
(function() {


}).call(this);
// This is a manifest file that'll be compiled into application.js, which will include all the files
// listed below.
//
// Any JavaScript/Coffee file within this directory, lib/assets/javascripts, vendor/assets/javascripts,
// or any plugin's vendor/assets/javascripts directory can be referenced here using a relative path.
//
// It's not advisable to add code directly here, but if you do, it'll appear at the bottom of the
// compiled file. JavaScript code in this file should be added after the last require_* statement.
//
// Read Sprockets README (https://github.com/rails/sprockets#sprockets-directives) for details
// about supported directives.
//


// require turbolinks

// Turbolink fix: https://stackoverflow.com/questions/17600093/rails-javascript-not-loading-after-clicking-through-link-to-helper
var ready = function() {

    // Formatting sidebar
    if (typeof chapter_id !== 'undefined') {
        hightlight_sidebar(chapter_id);
    }

    $(window).scroll(function () {
        if ($(window).scrollTop() >= $(document).height() - $(window).height() - 5) {
            next_link = $('a.scroll-next:last').attr('href');
            next_chapter = $(".next-page:last");
            last_chapter = next_chapter.parent();

            if (next_link[next_link.length-1] !== 'e' ) {
                // Last chapter links to 'e' for end; however the link will be
                // expanded by wget, so we check for the last char of the link
                next_chapter.load(next_link + " .chapter-content",
                    function(responseTxt, statusTxt, xhr){
                        // There should be a better way than regex to get chapter id
                        var id_regex = /[0-9]+$/;
                        chapter_id = id_regex.exec(next_link);
                        $(".chapter-content:last").before("<hr/>");
                        newpage_ready();
                    }
                );
            }
        }
    });

    $("#search-button").click(function() {
        $('#gsc-i-id1').val($("#search-box").val());
        $('input.gsc-search-button').trigger("click");
    });
};

var newpage_ready = function() {
    hightlight_sidebar(chapter_id);
    PR.prettyPrint();
    MathJax.Hub.Queue(["Typeset",MathJax.Hub]);
}

function hightlight_sidebar(chapter_id) {
    $('.sidebar-active').removeClass('sidebar-active');
    var active_tab = $('#sidebar-'+chapter_id);
    active_tab.addClass('sidebar-active');
    var parent_tab = active_tab.parent();
    while (parent_tab.attr('id') != 'nav-sidebar') {
        parent_tab.collapse('show');
        parent_tab = parent_tab.parent();
    }
}

$(document).ready(ready);
$(document).on('page:change', ready);
