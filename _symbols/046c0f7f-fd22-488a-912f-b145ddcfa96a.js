// Contact Form - Updated February 16, 2025
function noop() { }
function run(fn) {
    return fn();
}
function blank_object() {
    return Object.create(null);
}
function run_all(fns) {
    fns.forEach(run);
}
function is_function(thing) {
    return typeof thing === 'function';
}
function safe_not_equal(a, b) {
    return a != a ? b == b : a !== b || ((a && typeof a === 'object') || typeof a === 'function');
}
function is_empty(obj) {
    return Object.keys(obj).length === 0;
}

// Track which nodes are claimed during hydration. Unclaimed nodes can then be removed from the DOM
// at the end of hydration without touching the remaining nodes.
let is_hydrating = false;
function start_hydrating() {
    is_hydrating = true;
}
function end_hydrating() {
    is_hydrating = false;
}
function upper_bound(low, high, key, value) {
    // Return first index of value larger than input value in the range [low, high)
    while (low < high) {
        const mid = low + ((high - low) >> 1);
        if (key(mid) <= value) {
            low = mid + 1;
        }
        else {
            high = mid;
        }
    }
    return low;
}
function init_hydrate(target) {
    if (target.hydrate_init)
        return;
    target.hydrate_init = true;
    // We know that all children have claim_order values since the unclaimed have been detached if target is not <head>
    let children = target.childNodes;
    // If target is <head>, there may be children without claim_order
    if (target.nodeName === 'HEAD') {
        const myChildren = [];
        for (let i = 0; i < children.length; i++) {
            const node = children[i];
            if (node.claim_order !== undefined) {
                myChildren.push(node);
            }
        }
        children = myChildren;
    }
    /*
    * Reorder claimed children optimally.
    * We can reorder claimed children optimally by finding the longest subsequence of
    * nodes that are already claimed in order and only moving the rest. The longest
    * subsequence of nodes that are claimed in order can be found by
    * computing the longest increasing subsequence of .claim_order values.
    *
    * This algorithm is optimal in generating the least amount of reorder operations
    * possible.
    *
    * Proof:
    * We know that, given a set of reordering operations, the nodes that do not move
    * always form an increasing subsequence, since they do not move among each other
    * meaning that they must be already ordered among each other. Thus, the maximal
    * set of nodes that do not move form a longest increasing subsequence.
    */
    // Compute longest increasing subsequence
    // m: subsequence length j => index k of smallest value that ends an increasing subsequence of length j
    const m = new Int32Array(children.length + 1);
    // Predecessor indices + 1
    const p = new Int32Array(children.length);
    m[0] = -1;
    let longest = 0;
    for (let i = 0; i < children.length; i++) {
        const current = children[i].claim_order;
        // Find the largest subsequence length such that it ends in a value less than our current value
        // upper_bound returns first greater value, so we subtract one
        // with fast path for when we are on the current longest subsequence
        const seqLen = ((longest > 0 && children[m[longest]].claim_order <= current) ? longest + 1 : upper_bound(1, longest, idx => children[m[idx]].claim_order, current)) - 1;
        p[i] = m[seqLen] + 1;
        const newLen = seqLen + 1;
        // We can guarantee that current is the smallest value. Otherwise, we would have generated a longer sequence.
        m[newLen] = i;
        longest = Math.max(newLen, longest);
    }
    // The longest increasing subsequence of nodes (initially reversed)
    const lis = [];
    // The rest of the nodes, nodes that will be moved
    const toMove = [];
    let last = children.length - 1;
    for (let cur = m[longest] + 1; cur != 0; cur = p[cur - 1]) {
        lis.push(children[cur - 1]);
        for (; last >= cur; last--) {
            toMove.push(children[last]);
        }
        last--;
    }
    for (; last >= 0; last--) {
        toMove.push(children[last]);
    }
    lis.reverse();
    // We sort the nodes being moved to guarantee that their insertion order matches the claim order
    toMove.sort((a, b) => a.claim_order - b.claim_order);
    // Finally, we move the nodes
    for (let i = 0, j = 0; i < toMove.length; i++) {
        while (j < lis.length && toMove[i].claim_order >= lis[j].claim_order) {
            j++;
        }
        const anchor = j < lis.length ? lis[j] : null;
        target.insertBefore(toMove[i], anchor);
    }
}
function append_hydration(target, node) {
    if (is_hydrating) {
        init_hydrate(target);
        if ((target.actual_end_child === undefined) || ((target.actual_end_child !== null) && (target.actual_end_child.parentNode !== target))) {
            target.actual_end_child = target.firstChild;
        }
        // Skip nodes of undefined ordering
        while ((target.actual_end_child !== null) && (target.actual_end_child.claim_order === undefined)) {
            target.actual_end_child = target.actual_end_child.nextSibling;
        }
        if (node !== target.actual_end_child) {
            // We only insert if the ordering of this node should be modified or the parent node is not target
            if (node.claim_order !== undefined || node.parentNode !== target) {
                target.insertBefore(node, target.actual_end_child);
            }
        }
        else {
            target.actual_end_child = node.nextSibling;
        }
    }
    else if (node.parentNode !== target || node.nextSibling !== null) {
        target.appendChild(node);
    }
}
function insert_hydration(target, node, anchor) {
    if (is_hydrating && !anchor) {
        append_hydration(target, node);
    }
    else if (node.parentNode !== target || node.nextSibling != anchor) {
        target.insertBefore(node, anchor || null);
    }
}
function detach(node) {
    if (node.parentNode) {
        node.parentNode.removeChild(node);
    }
}
function destroy_each(iterations, detaching) {
    for (let i = 0; i < iterations.length; i += 1) {
        if (iterations[i])
            iterations[i].d(detaching);
    }
}
function element(name) {
    return document.createElement(name);
}
function text(data) {
    return document.createTextNode(data);
}
function space() {
    return text(' ');
}
function attr(node, attribute, value) {
    if (value == null)
        node.removeAttribute(attribute);
    else if (node.getAttribute(attribute) !== value)
        node.setAttribute(attribute, value);
}
function children(element) {
    return Array.from(element.childNodes);
}
function init_claim_info(nodes) {
    if (nodes.claim_info === undefined) {
        nodes.claim_info = { last_index: 0, total_claimed: 0 };
    }
}
function claim_node(nodes, predicate, processNode, createNode, dontUpdateLastIndex = false) {
    // Try to find nodes in an order such that we lengthen the longest increasing subsequence
    init_claim_info(nodes);
    const resultNode = (() => {
        // We first try to find an element after the previous one
        for (let i = nodes.claim_info.last_index; i < nodes.length; i++) {
            const node = nodes[i];
            if (predicate(node)) {
                const replacement = processNode(node);
                if (replacement === undefined) {
                    nodes.splice(i, 1);
                }
                else {
                    nodes[i] = replacement;
                }
                if (!dontUpdateLastIndex) {
                    nodes.claim_info.last_index = i;
                }
                return node;
            }
        }
        // Otherwise, we try to find one before
        // We iterate in reverse so that we don't go too far back
        for (let i = nodes.claim_info.last_index - 1; i >= 0; i--) {
            const node = nodes[i];
            if (predicate(node)) {
                const replacement = processNode(node);
                if (replacement === undefined) {
                    nodes.splice(i, 1);
                }
                else {
                    nodes[i] = replacement;
                }
                if (!dontUpdateLastIndex) {
                    nodes.claim_info.last_index = i;
                }
                else if (replacement === undefined) {
                    // Since we spliced before the last_index, we decrease it
                    nodes.claim_info.last_index--;
                }
                return node;
            }
        }
        // If we can't find any matching node, we create a new one
        return createNode();
    })();
    resultNode.claim_order = nodes.claim_info.total_claimed;
    nodes.claim_info.total_claimed += 1;
    return resultNode;
}
function claim_element_base(nodes, name, attributes, create_element) {
    return claim_node(nodes, (node) => node.nodeName === name, (node) => {
        const remove = [];
        for (let j = 0; j < node.attributes.length; j++) {
            const attribute = node.attributes[j];
            if (!attributes[attribute.name]) {
                remove.push(attribute.name);
            }
        }
        remove.forEach(v => node.removeAttribute(v));
        return undefined;
    }, () => create_element(name));
}
function claim_element(nodes, name, attributes) {
    return claim_element_base(nodes, name, attributes, element);
}
function claim_text(nodes, data) {
    return claim_node(nodes, (node) => node.nodeType === 3, (node) => {
        const dataStr = '' + data;
        if (node.data.startsWith(dataStr)) {
            if (node.data.length !== dataStr.length) {
                return node.splitText(dataStr.length);
            }
        }
        else {
            node.data = dataStr;
        }
    }, () => text(data), true // Text nodes should not update last index since it is likely not worth it to eliminate an increasing subsequence of actual elements
    );
}
function claim_space(nodes) {
    return claim_text(nodes, ' ');
}
function set_data(text, data) {
    data = '' + data;
    if (text.data === data)
        return;
    text.data = data;
}

let current_component;
function set_current_component(component) {
    current_component = component;
}

const dirty_components = [];
const binding_callbacks = [];
let render_callbacks = [];
const flush_callbacks = [];
const resolved_promise = /* @__PURE__ */ Promise.resolve();
let update_scheduled = false;
function schedule_update() {
    if (!update_scheduled) {
        update_scheduled = true;
        resolved_promise.then(flush);
    }
}
function add_render_callback(fn) {
    render_callbacks.push(fn);
}
// flush() calls callbacks in this order:
// 1. All beforeUpdate callbacks, in order: parents before children
// 2. All bind:this callbacks, in reverse order: children before parents.
// 3. All afterUpdate callbacks, in order: parents before children. EXCEPT
//    for afterUpdates called during the initial onMount, which are called in
//    reverse order: children before parents.
// Since callbacks might update component values, which could trigger another
// call to flush(), the following steps guard against this:
// 1. During beforeUpdate, any updated components will be added to the
//    dirty_components array and will cause a reentrant call to flush(). Because
//    the flush index is kept outside the function, the reentrant call will pick
//    up where the earlier call left off and go through all dirty components. The
//    current_component value is saved and restored so that the reentrant call will
//    not interfere with the "parent" flush() call.
// 2. bind:this callbacks cannot trigger new flush() calls.
// 3. During afterUpdate, any updated components will NOT have their afterUpdate
//    callback called a second time; the seen_callbacks set, outside the flush()
//    function, guarantees this behavior.
const seen_callbacks = new Set();
let flushidx = 0; // Do *not* move this inside the flush() function
function flush() {
    // Do not reenter flush while dirty components are updated, as this can
    // result in an infinite loop. Instead, let the inner flush handle it.
    // Reentrancy is ok afterwards for bindings etc.
    if (flushidx !== 0) {
        return;
    }
    const saved_component = current_component;
    do {
        // first, call beforeUpdate functions
        // and update components
        try {
            while (flushidx < dirty_components.length) {
                const component = dirty_components[flushidx];
                flushidx++;
                set_current_component(component);
                update(component.$$);
            }
        }
        catch (e) {
            // reset dirty state to not end up in a deadlocked state and then rethrow
            dirty_components.length = 0;
            flushidx = 0;
            throw e;
        }
        set_current_component(null);
        dirty_components.length = 0;
        flushidx = 0;
        while (binding_callbacks.length)
            binding_callbacks.pop()();
        // then, once components are updated, call
        // afterUpdate functions. This may cause
        // subsequent updates...
        for (let i = 0; i < render_callbacks.length; i += 1) {
            const callback = render_callbacks[i];
            if (!seen_callbacks.has(callback)) {
                // ...so guard against infinite loops
                seen_callbacks.add(callback);
                callback();
            }
        }
        render_callbacks.length = 0;
    } while (dirty_components.length);
    while (flush_callbacks.length) {
        flush_callbacks.pop()();
    }
    update_scheduled = false;
    seen_callbacks.clear();
    set_current_component(saved_component);
}
function update($$) {
    if ($$.fragment !== null) {
        $$.update();
        run_all($$.before_update);
        const dirty = $$.dirty;
        $$.dirty = [-1];
        $$.fragment && $$.fragment.p($$.ctx, dirty);
        $$.after_update.forEach(add_render_callback);
    }
}
/**
 * Useful for example to execute remaining `afterUpdate` callbacks before executing `destroy`.
 */
function flush_render_callbacks(fns) {
    const filtered = [];
    const targets = [];
    render_callbacks.forEach((c) => fns.indexOf(c) === -1 ? filtered.push(c) : targets.push(c));
    targets.forEach((c) => c());
    render_callbacks = filtered;
}
const outroing = new Set();
function transition_in(block, local) {
    if (block && block.i) {
        outroing.delete(block);
        block.i(local);
    }
}
function mount_component(component, target, anchor, customElement) {
    const { fragment, after_update } = component.$$;
    fragment && fragment.m(target, anchor);
    if (!customElement) {
        // onMount happens before the initial afterUpdate
        add_render_callback(() => {
            const new_on_destroy = component.$$.on_mount.map(run).filter(is_function);
            // if the component was destroyed immediately
            // it will update the `$$.on_destroy` reference to `null`.
            // the destructured on_destroy may still reference to the old array
            if (component.$$.on_destroy) {
                component.$$.on_destroy.push(...new_on_destroy);
            }
            else {
                // Edge case - component was destroyed immediately,
                // most likely as a result of a binding initialising
                run_all(new_on_destroy);
            }
            component.$$.on_mount = [];
        });
    }
    after_update.forEach(add_render_callback);
}
function destroy_component(component, detaching) {
    const $$ = component.$$;
    if ($$.fragment !== null) {
        flush_render_callbacks($$.after_update);
        run_all($$.on_destroy);
        $$.fragment && $$.fragment.d(detaching);
        // TODO null out other refs, including component.$$ (but need to
        // preserve final state?)
        $$.on_destroy = $$.fragment = null;
        $$.ctx = [];
    }
}
function make_dirty(component, i) {
    if (component.$$.dirty[0] === -1) {
        dirty_components.push(component);
        schedule_update();
        component.$$.dirty.fill(0);
    }
    component.$$.dirty[(i / 31) | 0] |= (1 << (i % 31));
}
function init(component, options, instance, create_fragment, not_equal, props, append_styles, dirty = [-1]) {
    const parent_component = current_component;
    set_current_component(component);
    const $$ = component.$$ = {
        fragment: null,
        ctx: [],
        // state
        props,
        update: noop,
        not_equal,
        bound: blank_object(),
        // lifecycle
        on_mount: [],
        on_destroy: [],
        on_disconnect: [],
        before_update: [],
        after_update: [],
        context: new Map(options.context || (parent_component ? parent_component.$$.context : [])),
        // everything else
        callbacks: blank_object(),
        dirty,
        skip_bound: false,
        root: options.target || parent_component.$$.root
    };
    append_styles && append_styles($$.root);
    let ready = false;
    $$.ctx = instance
        ? instance(component, options.props || {}, (i, ret, ...rest) => {
            const value = rest.length ? rest[0] : ret;
            if ($$.ctx && not_equal($$.ctx[i], $$.ctx[i] = value)) {
                if (!$$.skip_bound && $$.bound[i])
                    $$.bound[i](value);
                if (ready)
                    make_dirty(component, i);
            }
            return ret;
        })
        : [];
    $$.update();
    ready = true;
    run_all($$.before_update);
    // `false` as a special case of no DOM component
    $$.fragment = create_fragment ? create_fragment($$.ctx) : false;
    if (options.target) {
        if (options.hydrate) {
            start_hydrating();
            const nodes = children(options.target);
            // eslint-disable-next-line @typescript-eslint/no-non-null-assertion
            $$.fragment && $$.fragment.l(nodes);
            nodes.forEach(detach);
        }
        else {
            // eslint-disable-next-line @typescript-eslint/no-non-null-assertion
            $$.fragment && $$.fragment.c();
        }
        if (options.intro)
            transition_in(component.$$.fragment);
        mount_component(component, options.target, options.anchor, options.customElement);
        end_hydrating();
        flush();
    }
    set_current_component(parent_component);
}
/**
 * Base class for Svelte components. Used when dev=false.
 */
class SvelteComponent {
    $destroy() {
        destroy_component(this, 1);
        this.$destroy = noop;
    }
    $on(type, callback) {
        if (!is_function(callback)) {
            return noop;
        }
        const callbacks = (this.$$.callbacks[type] || (this.$$.callbacks[type] = []));
        callbacks.push(callback);
        return () => {
            const index = callbacks.indexOf(callback);
            if (index !== -1)
                callbacks.splice(index, 1);
        };
    }
    $set($$props) {
        if (this.$$set && !is_empty($$props)) {
            this.$$.skip_bound = true;
            this.$$set($$props);
            this.$$.skip_bound = false;
        }
    }
}

/* generated by Svelte v3.59.1 */

function get_each_context(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[5] = list[i].icon;
	child_ctx[6] = list[i].label;
	return child_ctx;
}

// (213:8) {#each list_items as { icon, label }}
function create_each_block(ctx) {
	let li;
	let span;
	let t0_value = /*label*/ ctx[6] + "";
	let t0;
	let t1;

	return {
		c() {
			li = element("li");
			span = element("span");
			t0 = text(t0_value);
			t1 = space();
			this.h();
		},
		l(nodes) {
			li = claim_element(nodes, "LI", { class: true });
			var li_nodes = children(li);
			span = claim_element(li_nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			t0 = claim_text(span_nodes, t0_value);
			span_nodes.forEach(detach);
			t1 = claim_space(li_nodes);
			li_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(span, "class", "label");
			attr(li, "class", "svelte-1cugjfd");
		},
		m(target, anchor) {
			insert_hydration(target, li, anchor);
			append_hydration(li, span);
			append_hydration(span, t0);
			append_hydration(li, t1);
		},
		p(ctx, dirty) {
			if (dirty & /*list_items*/ 2 && t0_value !== (t0_value = /*label*/ ctx[6] + "")) set_data(t0, t0_value);
		},
		d(detaching) {
			if (detaching) detach(li);
		}
	};
}

function create_fragment(ctx) {
	let section1;
	let div8;
	let div0;
	let h2;
	let t0;
	let t1;
	let h3;
	let t2;
	let t3;
	let ul;
	let t4;
	let input0;
	let t5;
	let form_1;
	let section0;
	let div7;
	let div1;
	let label0;
	let t6;
	let t7;
	let input1;
	let t8;
	let div2;
	let label1;
	let t9;
	let t10;
	let input2;
	let t11;
	let div3;
	let label2;
	let t12;
	let t13;
	let textarea;
	let t14;
	let div4;
	let label3;
	let t15;
	let t16;
	let input3;
	let t17;
	let div5;
	let label4;
	let t18;
	let t19;
	let input4;
	let t20;
	let div6;
	let label5;
	let t21;
	let t22;
	let input5;
	let t23;
	let button;
	let t24;
	let each_value = /*list_items*/ ctx[1];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block(get_each_context(ctx, each_value, i));
	}

	return {
		c() {
			section1 = element("section");
			div8 = element("div");
			div0 = element("div");
			h2 = element("h2");
			t0 = text(/*heading*/ ctx[0]);
			t1 = space();
			h3 = element("h3");
			t2 = text(/*subheading*/ ctx[2]);
			t3 = space();
			ul = element("ul");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t4 = space();
			input0 = element("input");
			t5 = space();
			form_1 = element("form");
			section0 = element("section");
			div7 = element("div");
			div1 = element("div");
			label0 = element("label");
			t6 = text("Name");
			t7 = space();
			input1 = element("input");
			t8 = space();
			div2 = element("div");
			label1 = element("label");
			t9 = text("Email");
			t10 = space();
			input2 = element("input");
			t11 = space();
			div3 = element("div");
			label2 = element("label");
			t12 = text("Project Details");
			t13 = space();
			textarea = element("textarea");
			t14 = space();
			div4 = element("div");
			label3 = element("label");
			t15 = text("What is your book’s genre?");
			t16 = space();
			input3 = element("input");
			t17 = space();
			div5 = element("div");
			label4 = element("label");
			t18 = text("When would you like to work together?");
			t19 = space();
			input4 = element("input");
			t20 = space();
			div6 = element("div");
			label5 = element("label");
			t21 = text("What is your book cover budget? (In USD)");
			t22 = space();
			input5 = element("input");
			t23 = space();
			button = element("button");
			t24 = text("Submit");
			this.h();
		},
		l(nodes) {
			section1 = claim_element(nodes, "SECTION", { class: true });
			var section1_nodes = children(section1);
			div8 = claim_element(section1_nodes, "DIV", { class: true });
			var div8_nodes = children(div8);
			div0 = claim_element(div8_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			h2 = claim_element(div0_nodes, "H2", { class: true });
			var h2_nodes = children(h2);
			t0 = claim_text(h2_nodes, /*heading*/ ctx[0]);
			h2_nodes.forEach(detach);
			t1 = claim_space(div0_nodes);
			h3 = claim_element(div0_nodes, "H3", { class: true });
			var h3_nodes = children(h3);
			t2 = claim_text(h3_nodes, /*subheading*/ ctx[2]);
			h3_nodes.forEach(detach);
			t3 = claim_space(div0_nodes);
			ul = claim_element(div0_nodes, "UL", { class: true });
			var ul_nodes = children(ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(ul_nodes);
			}

			ul_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			t4 = claim_space(div8_nodes);
			input0 = claim_element(div8_nodes, "INPUT", { type: true, name: true, class: true });
			t5 = claim_space(div8_nodes);

			form_1 = claim_element(div8_nodes, "FORM", {
				target: true,
				action: true,
				method: true,
				class: true
			});

			var form_1_nodes = children(form_1);
			section0 = claim_element(form_1_nodes, "SECTION", { class: true });
			var section0_nodes = children(section0);
			div7 = claim_element(section0_nodes, "DIV", { class: true });
			var div7_nodes = children(div7);
			div1 = claim_element(div7_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			label0 = claim_element(div1_nodes, "LABEL", { for: true, class: true });
			var label0_nodes = children(label0);
			t6 = claim_text(label0_nodes, "Name");
			label0_nodes.forEach(detach);
			t7 = claim_space(div1_nodes);

			input1 = claim_element(div1_nodes, "INPUT", {
				id: true,
				name: true,
				class: true,
				placeholder: true,
				type: true
			});

			div1_nodes.forEach(detach);
			t8 = claim_space(div7_nodes);
			div2 = claim_element(div7_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			label1 = claim_element(div2_nodes, "LABEL", { for: true, class: true });
			var label1_nodes = children(label1);
			t9 = claim_text(label1_nodes, "Email");
			label1_nodes.forEach(detach);
			t10 = claim_space(div2_nodes);

			input2 = claim_element(div2_nodes, "INPUT", {
				id: true,
				name: true,
				class: true,
				placeholder: true,
				type: true
			});

			div2_nodes.forEach(detach);
			t11 = claim_space(div7_nodes);
			div3 = claim_element(div7_nodes, "DIV", { class: true });
			var div3_nodes = children(div3);
			label2 = claim_element(div3_nodes, "LABEL", { for: true, class: true });
			var label2_nodes = children(label2);
			t12 = claim_text(label2_nodes, "Project Details");
			label2_nodes.forEach(detach);
			t13 = claim_space(div3_nodes);

			textarea = claim_element(div3_nodes, "TEXTAREA", {
				class: true,
				id: true,
				name: true,
				placeholder: true
			});

			children(textarea).forEach(detach);
			div3_nodes.forEach(detach);
			t14 = claim_space(div7_nodes);
			div4 = claim_element(div7_nodes, "DIV", { class: true });
			var div4_nodes = children(div4);
			label3 = claim_element(div4_nodes, "LABEL", { for: true, class: true });
			var label3_nodes = children(label3);
			t15 = claim_text(label3_nodes, "What is your book’s genre?");
			label3_nodes.forEach(detach);
			t16 = claim_space(div4_nodes);

			input3 = claim_element(div4_nodes, "INPUT", {
				id: true,
				name: true,
				class: true,
				placeholder: true,
				type: true
			});

			div4_nodes.forEach(detach);
			t17 = claim_space(div7_nodes);
			div5 = claim_element(div7_nodes, "DIV", { class: true });
			var div5_nodes = children(div5);
			label4 = claim_element(div5_nodes, "LABEL", { for: true, class: true });
			var label4_nodes = children(label4);
			t18 = claim_text(label4_nodes, "When would you like to work together?");
			label4_nodes.forEach(detach);
			t19 = claim_space(div5_nodes);

			input4 = claim_element(div5_nodes, "INPUT", {
				id: true,
				name: true,
				class: true,
				placeholder: true,
				type: true
			});

			div5_nodes.forEach(detach);
			t20 = claim_space(div7_nodes);
			div6 = claim_element(div7_nodes, "DIV", { class: true });
			var div6_nodes = children(div6);
			label5 = claim_element(div6_nodes, "LABEL", { for: true, class: true });
			var label5_nodes = children(label5);
			t21 = claim_text(label5_nodes, "What is your book cover budget? (In USD)");
			label5_nodes.forEach(detach);
			t22 = claim_space(div6_nodes);

			input5 = claim_element(div6_nodes, "INPUT", {
				id: true,
				name: true,
				class: true,
				placeholder: true,
				type: true
			});

			div6_nodes.forEach(detach);
			div7_nodes.forEach(detach);
			section0_nodes.forEach(detach);
			t23 = claim_space(form_1_nodes);
			button = claim_element(form_1_nodes, "BUTTON", { type: true, class: true });
			var button_nodes = children(button);
			t24 = claim_text(button_nodes, "Submit");
			button_nodes.forEach(detach);
			form_1_nodes.forEach(detach);
			div8_nodes.forEach(detach);
			section1_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h2, "class", "heading");
			attr(h3, "class", "subheading svelte-1cugjfd");
			attr(ul, "class", "svelte-1cugjfd");
			attr(div0, "class", "main svelte-1cugjfd");
			attr(input0, "type", "hidden");
			attr(input0, "name", "_captcha");
			input0.value = "false";
			attr(input0, "class", "svelte-1cugjfd");
			attr(label0, "for", "name");
			attr(label0, "class", "form-label svelte-1cugjfd");
			attr(input1, "id", "name");
			attr(input1, "name", "name");
			attr(input1, "class", "form-input svelte-1cugjfd");
			attr(input1, "placeholder", "Full Name");
			attr(input1, "type", "text");
			attr(div1, "class", "form-group svelte-1cugjfd");
			attr(label1, "for", "email");
			attr(label1, "class", "form-label svelte-1cugjfd");
			attr(input2, "id", "email");
			attr(input2, "name", "email");
			attr(input2, "class", "form-input svelte-1cugjfd");
			attr(input2, "placeholder", "Your email");
			attr(input2, "type", "email");
			attr(div2, "class", "form-group svelte-1cugjfd");
			attr(label2, "for", "message");
			attr(label2, "class", "form-label svelte-1cugjfd");
			attr(textarea, "class", "form-textarea svelte-1cugjfd");
			attr(textarea, "id", "message");
			attr(textarea, "name", "message");
			attr(textarea, "placeholder", "Your project details");
			attr(div3, "class", "form-group svelte-1cugjfd");
			attr(label3, "for", "genre");
			attr(label3, "class", "form-label svelte-1cugjfd");
			attr(input3, "id", "genre");
			attr(input3, "name", "genre");
			attr(input3, "class", "form-input svelte-1cugjfd");
			attr(input3, "placeholder", "Genre");
			attr(input3, "type", "text");
			attr(div4, "class", "form-group svelte-1cugjfd");
			attr(label4, "for", "when");
			attr(label4, "class", "form-label svelte-1cugjfd");
			attr(input4, "id", "when");
			attr(input4, "name", "when");
			attr(input4, "class", "form-input svelte-1cugjfd");
			attr(input4, "placeholder", "");
			attr(input4, "type", "text");
			attr(div5, "class", "form-group svelte-1cugjfd");
			attr(label5, "for", "Budget");
			attr(label5, "class", "form-label svelte-1cugjfd");
			attr(input5, "id", "Budget");
			attr(input5, "name", "Budget");
			attr(input5, "class", "form-input svelte-1cugjfd");
			attr(input5, "placeholder", "");
			attr(input5, "type", "text");
			attr(div6, "class", "form-group svelte-1cugjfd");
			attr(div7, "class", "form-group-container svelte-1cugjfd");
			attr(section0, "class", "contact-section svelte-1cugjfd");
			attr(button, "type", "submit");
			attr(button, "class", "button svelte-1cugjfd");
			attr(form_1, "target", "_blank");
			attr(form_1, "action", "https://formsubmit.co/bookishforge@gmail.com");
			attr(form_1, "method", "POST");
			attr(form_1, "class", "svelte-1cugjfd");
			attr(div8, "class", "section-container svelte-1cugjfd");
			attr(section1, "class", "section svelte-1cugjfd");
		},
		m(target, anchor) {
			insert_hydration(target, section1, anchor);
			append_hydration(section1, div8);
			append_hydration(div8, div0);
			append_hydration(div0, h2);
			append_hydration(h2, t0);
			append_hydration(div0, t1);
			append_hydration(div0, h3);
			append_hydration(h3, t2);
			append_hydration(div0, t3);
			append_hydration(div0, ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(ul, null);
				}
			}

			append_hydration(div8, t4);
			append_hydration(div8, input0);
			append_hydration(div8, t5);
			append_hydration(div8, form_1);
			append_hydration(form_1, section0);
			append_hydration(section0, div7);
			append_hydration(div7, div1);
			append_hydration(div1, label0);
			append_hydration(label0, t6);
			append_hydration(div1, t7);
			append_hydration(div1, input1);
			append_hydration(div7, t8);
			append_hydration(div7, div2);
			append_hydration(div2, label1);
			append_hydration(label1, t9);
			append_hydration(div2, t10);
			append_hydration(div2, input2);
			append_hydration(div7, t11);
			append_hydration(div7, div3);
			append_hydration(div3, label2);
			append_hydration(label2, t12);
			append_hydration(div3, t13);
			append_hydration(div3, textarea);
			append_hydration(div7, t14);
			append_hydration(div7, div4);
			append_hydration(div4, label3);
			append_hydration(label3, t15);
			append_hydration(div4, t16);
			append_hydration(div4, input3);
			append_hydration(div7, t17);
			append_hydration(div7, div5);
			append_hydration(div5, label4);
			append_hydration(label4, t18);
			append_hydration(div5, t19);
			append_hydration(div5, input4);
			append_hydration(div7, t20);
			append_hydration(div7, div6);
			append_hydration(div6, label5);
			append_hydration(label5, t21);
			append_hydration(div6, t22);
			append_hydration(div6, input5);
			append_hydration(form_1, t23);
			append_hydration(form_1, button);
			append_hydration(button, t24);
		},
		p(ctx, [dirty]) {
			if (dirty & /*heading*/ 1) set_data(t0, /*heading*/ ctx[0]);
			if (dirty & /*subheading*/ 4) set_data(t2, /*subheading*/ ctx[2]);

			if (dirty & /*list_items*/ 2) {
				each_value = /*list_items*/ ctx[1];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(ul, null);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(section1);
			destroy_each(each_blocks, detaching);
		}
	};
}

function instance($$self, $$props, $$invalidate) {
	let { props } = $$props;
	let { form } = $$props;
	let { heading } = $$props;
	let { list_items } = $$props;
	let { subheading } = $$props;

	$$self.$$set = $$props => {
		if ('props' in $$props) $$invalidate(3, props = $$props.props);
		if ('form' in $$props) $$invalidate(4, form = $$props.form);
		if ('heading' in $$props) $$invalidate(0, heading = $$props.heading);
		if ('list_items' in $$props) $$invalidate(1, list_items = $$props.list_items);
		if ('subheading' in $$props) $$invalidate(2, subheading = $$props.subheading);
	};

	return [heading, list_items, subheading, props, form];
}

class Component extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance, create_fragment, safe_not_equal, {
			props: 3,
			form: 4,
			heading: 0,
			list_items: 1,
			subheading: 2
		});
	}
}

export { Component as default };
