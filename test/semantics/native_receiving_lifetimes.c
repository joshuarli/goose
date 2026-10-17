static size_t node_count(gir_control_graph *graph) {
    size_t count = 0;
    for (gir_control_attempt *node = graph->attempts; node; node = node->next) count++;
    return count;
}
static void normal_call(void) {
    uint8_t bytes[128] = {0};
    gs_stack stack = {0};
    stack.top = bytes;
    uint8_t *caller = gir_control_enter();
    uint8_t *receiver = gir_control_receiving_new((uint8_t *)&stack, bytes, 17, 0);
    uint8_t *raw = gir_control_receiving_current(receiver);
    uint8_t *inputs[] = { raw };
    uint8_t *call = gir_control_call_push(1, inputs, 0, NULL);
    uint8_t *callee = gir_control_enter();
    uint8_t *incoming = gir_control_call_param(0);
    uint8_t *entry = gir_control_receiving_current(incoming);
    gir_control_require(gir_control_receiving_open(entry) == incoming);
    uint8_t *built = gir_control_receiving_current(incoming);
    ((gir_control_metadata *)built)->count = 1;
    gir_control_attempt_finish(built);
    gir_control_attempt_return(built);
    gir_control_leave(callee);
    uint8_t *result = gir_control_call_get(call, 0);
    gir_control_require(((gir_control_metadata *)result)->count == 1);
    gir_control_require(((gir_control_metadata *)result)->identity == 17);
    gir_control_require(*(int64_t *)gir_control_attempt_progress(result) == GIR_CONTROL_BUILT);
    gir_control_call_pop(call);
    gir_control_attempt_publish(result);
    gir_control_leave(caller);
}
static void cancelled_retries(void) {
    uint8_t bytes[128] = {0};
    gs_stack stack = {0};
    stack.top = bytes;
    uint8_t *scope = gir_control_enter();
    uint8_t *receiver = gir_control_receiving_new((uint8_t *)&stack, bytes, 0, 0);
    uint8_t *entry = gir_control_receiving_current(receiver);
    gir_control_receiving_open(entry);
    uint8_t *historical = gir_control_receiving_renew(receiver);
    uint8_t *outer = gir_control_exit_reserve(receiver, 0, NULL);
    uint8_t *writer = gir_control_exit_selected(outer);
    gir_control_graph *graph = ((gir_control_receiving *)receiver)->graph;
    for (int retry = 0; retry < 1000; retry++) {
        uint8_t *ticket = gir_control_exit_reserve(receiver, 0, NULL);
        uint8_t *selected = gir_control_exit_selected(ticket);
        ((gir_control_metadata *)selected)->count = 1;
        stack.top = bytes + 1;
        gir_control_exit_discard(ticket, 0, NULL);
        uint8_t *old = writer;
        writer = gir_control_receiving_refresh(receiver, writer, gir_control_attempt_start(writer), 0);
        gir_control_require(writer != old && gir_control_node(writer) != gir_control_node(historical));
        gir_control_require(((gir_control_metadata *)historical)->identity == 0);
        gir_control_require(node_count(graph) <= 2);
    }
    gir_control_attempt_finish(writer);
    uint8_t *start = gir_control_exit_prepare(outer, writer);
    gir_control_exit_commit(outer, writer, start);
    gir_control_exit_release(outer);
    gir_control_attempt_return(historical);
    gir_control_attempt_publish(writer);
    gir_control_leave(scope);
}

static void bounded_call(void) {
    uint8_t bytes[128] = {0};
    gs_stack stack = {0};
    stack.top = bytes;
    uint8_t *scope = gir_control_enter();
    uint8_t *receiver = gir_control_receiving_new((uint8_t *)&stack, bytes, 31, 0);
    uint8_t *original = gir_control_receiving_current(receiver);
    gir_control_receiving_open(original);
    original = gir_control_receiving_renew(receiver);
    bytes[0] = 65;
    stack.top++;
    ((gir_control_metadata *)original)->count = 1;
    gir_control_attempt_finish(original);
    uint8_t *outer = gir_control_exit_reserve(receiver, 0, NULL);
    uint8_t *selected = gir_control_exit_selected(outer);
    uint8_t *inputs[] = {selected};
    uint8_t *call = gir_control_call_push(1, inputs, 0, NULL);
    uint8_t *callee = gir_control_enter();
    uint8_t *incoming = gir_control_call_param(0);
    uint8_t *raw = gir_control_receiving_current(incoming);
    gir_control_receiving_open(raw);
    uint8_t *inner = gir_control_exit_reserve(incoming, 0, NULL);
    raw = gir_control_exit_selected(inner);
    bytes[1] = 66;
    stack.top++;
    ((gir_control_metadata *)raw)->count = 1;
    gir_control_attempt_finish(raw);
    uint8_t *start = gir_control_exit_prepare(inner, raw);
    gir_control_require(start == bytes + 1);
    gir_control_exit_commit(inner, raw, start);
    gir_control_exit_release(inner);
    gir_control_attempt_return(raw);
    gir_control_leave(callee);
    raw = gir_control_call_get(call, 0);
    gir_control_call_pop(call);
    gir_control_require(gir_control_node(original)->progress == GIR_CONTROL_EXITING);
    gir_control_exit_discard(outer, 0, NULL);
    gir_control_require(gir_control_node(original)->progress == GIR_CONTROL_BUILT && stack.top == bytes + 1 && bytes[0] == 65);
    gir_control_attempt_publish(original);
    gir_control_leave(scope);
}
static void target_handoff(void) {
    uint8_t bytes[128] = {0};
    gs_stack stack = {0};
    stack.top = bytes;
    uint8_t *scope = gir_control_enter();
    uint8_t *receiver = gir_control_receiving_new((uint8_t *)&stack, bytes, 51, 0);
    uint8_t *raw = gir_control_receiving_current(receiver);
    gir_control_receiving_open(raw);
    raw = gir_control_receiving_renew(receiver);
    uint8_t *inputs[] = {raw};
    uint8_t *call = gir_control_call_push(1, inputs, 0, NULL);
    uint8_t *callee = gir_control_enter();
    uint8_t *incoming = gir_control_call_param(0);
    uint8_t *entry = gir_control_receiving_current(incoming);
    gir_control_receiving_open(entry);
    uint8_t *ticket = gir_control_exit_reserve(receiver, 0, NULL);
    raw = gir_control_exit_selected(ticket);
    stack.top++;
    ((gir_control_metadata *)raw)->count = 1;
    gir_control_attempt_finish(raw);
    gir_control_exit_release(ticket);
    gir_control_receiving_transfer(receiver, raw, gir_control_attempt_mode(raw));
    gir_control_attempt_return(raw);
    gir_control_leave(callee);
    raw = gir_control_receiving_current(receiver);
    uint8_t *cancelled = gir_control_call_get(call, 0);
    gir_control_call_pop(call);
    uint8_t *carried[] = {raw};
    gir_control_attempt_abandon(cancelled, 1, carried);
    gir_control_attempt_cancel(cancelled);
    ticket = gir_control_exit_adopt(receiver, raw);
    uint8_t *start = gir_control_exit_prepare(ticket, raw);
    gir_control_exit_commit(ticket, raw, start);
    gir_control_exit_release(ticket);
    gir_control_attempt_publish(raw);
    gir_control_leave(scope);
}
static void completed_aliases(void) {
    uint8_t bytes[4096] = {0};
    gs_stack stack = {0};
    stack.top = bytes;
    uint8_t *scope = gir_control_enter();
    uint8_t *receiver = gir_control_receiving_new((uint8_t *)&stack, bytes, 71, 0);
    uint8_t *parent = gir_control_receiving_current(receiver);
    gir_control_receiving_open(parent);
    parent = gir_control_receiving_renew(receiver);
    for (int index = 0; index < 1000; index++) {
        uint8_t *child_receiver = gir_control_receiving_new((uint8_t *)&stack, stack.top, index, 0);
        uint8_t *child = gir_control_receiving_current(child_receiver);
        gir_control_attempt_child(parent, child);
        gir_control_require(gir_control_receiving_open(child) == child_receiver);
        child = gir_control_receiving_renew(child_receiver);
        stack.top++;
        ((gir_control_metadata *)child)->count = 1;
        gir_control_attempt_finish(child);
        gir_control_receiving_drop(child_receiver);
        gir_control_require(gir_control_scope_top->receivers->next == NULL);
        gir_control_attempt_attach(parent, child);
        ((gir_control_metadata *)parent)->count++;
        gir_control_require(gir_control_scope_top->leases->next == NULL);
    }
    gir_control_attempt_finish(parent);
    gir_control_attempt_publish(parent);
    gir_control_leave(scope);
}
static void named_owner_bindings(void) {
    uint8_t bytes[4096] = {0};
    gs_stack stack = {0};
    stack.top = bytes;
    uint8_t *scope = gir_control_enter();
    uint8_t *receiver = gir_control_receiving_new((uint8_t *)&stack, bytes, 81, 0);
    uint8_t *raw = gir_control_receiving_current(receiver);
    gir_control_receiving_open(raw);
    raw = gir_control_receiving_renew(receiver);
    stack.top++;
    ((gir_control_metadata *)raw)->count = 1;
    gir_control_attempt_finish(raw);
    gir_hdr header = { bytes, 1 };
    uint8_t *binding = gir_control_owner_bind(receiver, (uint8_t *)&header, (uint8_t *)&stack);
    gir_control_attempt_return(raw);
    for (int index = 0; index < 1000; index++) {
        uint8_t *bindings[] = { binding, NULL };
        uint8_t *call = gir_control_call_push(0, NULL, 2, bindings);
        uint8_t *callee = gir_control_enter();
        uint8_t *borrowed = gir_control_owner_param(1);
        gir_control_owner_check(borrowed);
        stack.top++;
        header.len++;
        gir_control_owner_update(borrowed, header.len, stack.top);
        gir_control_owner_result(borrowed, 2);
        gir_control_leave(callee);
        gir_control_require(gir_control_owner_get(call, 2) == binding);
        gir_control_call_pop(call);
        gir_control_require(gir_control_scope_top->owners->next == NULL);
        gir_control_require(node_count(((gir_control_receiving *)receiver)->graph) == 1);
    }
    uint8_t *ticket = gir_control_exit_reserve(receiver, 1, binding);
    gir_control_exit_mark_named(ticket);
    raw = gir_control_exit_selected(ticket);
    gir_control_require(((gir_control_metadata *)raw)->count == 1001);
    uint8_t *start = gir_control_exit_prepare(ticket, raw);
    gir_control_exit_commit(ticket, raw, start);
    gir_control_exit_release(ticket);
    gir_control_attempt_publish(raw);
    gir_control_leave(scope);
}
static void cancellation_certificate(void) {
    uint8_t bytes[128] = {0};
    gs_stack stack = {0};
    stack.top = bytes;
    uint8_t *scope = gir_control_enter();
    uint8_t *receiver = gir_control_receiving_new((uint8_t *)&stack, bytes, 91, 0);
    uint8_t *raw = gir_control_receiving_current(receiver);
    gir_control_receiving_open(raw);
    uint8_t *ticket = gir_control_exit_reserve(receiver, 0, NULL);
    raw = gir_control_exit_selected(ticket);
    stack.top++;
    ((gir_control_metadata *)raw)->count = 1;
    uint8_t *certificate = gir_control_receiving_cancel(receiver, 0, NULL);
    gir_control_exit_discard(ticket, 0, NULL);
    gir_control_attempt_cancel(certificate);
    gir_control_require(stack.top == bytes);
    gir_control_leave(scope);
}
static void historical_named_source(void) {
    uint8_t bytes[128] = {0};
    gs_stack stack = {0};
    stack.top = bytes;
    uint8_t *scope = gir_control_enter();
    uint8_t *receiver = gir_control_receiving_new((uint8_t *)&stack, bytes, 0, 0);
    uint8_t *raw = gir_control_receiving_current(receiver);
    gir_control_receiving_open(raw);
    raw = gir_control_receiving_renew(receiver);
    stack.top++;
    ((gir_control_metadata *)raw)->count = 1;
    gir_control_attempt_finish(raw);
    uint8_t *source = gir_control_named_bind(raw);
    gir_control_attempt_return(raw);
    uint8_t *ticket = gir_control_exit_reserve(receiver, 0, NULL);
    raw = gir_control_exit_selected(ticket);
    stack.top++;
    ((gir_control_metadata *)raw)->count = 1;
    gir_control_attempt_finish(raw);
    uint8_t *start = gir_control_exit_prepare(ticket, raw);
    memmove(start, gir_control_attempt_start(raw), 1);
    stack.top = start + 1;
    gir_control_exit_commit(ticket, raw, start);
    gir_control_exit_release(ticket);
    ticket = gir_control_exit_reserve(receiver, 1, source);
    gir_control_require(!gir_control_exit_is_named(ticket));
    gir_control_exit_discard(ticket, 0, NULL);
    gir_control_attempt_publish(raw);
    gir_control_leave(scope);
}
static void displaced_child_cleanup(void) {
    uint8_t bytes[128] = {0};
    gs_stack stack = {0};
    stack.top = bytes;
    uint8_t *scope = gir_control_enter();
    uint8_t *receiver = gir_control_receiving_new((uint8_t *)&stack, bytes, 101, 0);
    uint8_t *parent = gir_control_receiving_current(receiver);
    uint8_t *child_receiver = gir_control_receiving_new((uint8_t *)&stack, bytes, 102, 0);
    uint8_t *child = gir_control_receiving_current(child_receiver);
    gir_control_attempt_child(parent, child);
    uint8_t *ticket = gir_control_exit_reserve(receiver, 0, NULL);
    uint8_t *replacement = gir_control_exit_selected(ticket);
    gir_control_attempt_finish(replacement);
    uint8_t *carried[] = { replacement };
    gir_control_abandon_tree(gir_control_node(parent), 1, carried);
    gir_control_require(gir_control_node(child)->progress == GIR_CONTROL_ABANDONED);
    gir_control_require(gir_control_node(replacement)->progress == GIR_CONTROL_BUILT);
    gir_control_exit_release(ticket);
    gir_control_leave(scope);
}
static void owner_extension(int outcome) {
    uint8_t bytes[128] = {0};
    gs_stack stack = {0};
    stack.top = bytes;
    uint8_t *scope = gir_control_enter();
    uint8_t *receiver = gir_control_receiving_new((uint8_t *)&stack, bytes, 111, 0);
    uint8_t *raw = gir_control_receiving_current(receiver);
    gir_control_receiving_open(raw);
    raw = gir_control_receiving_renew(receiver);
    stack.top++;
    ((gir_control_metadata *)raw)->count = 1;
    gir_control_attempt_finish(raw);
    gir_hdr header = {bytes, 1};
    uint8_t *binding = gir_control_owner_bind(receiver, (uint8_t *)&header, (uint8_t *)&stack);
    gir_control_attempt_return(raw);
    uint8_t *child_receiver = gir_control_receiving_new((uint8_t *)&stack, stack.top, 112, 0);
    uint8_t *child = gir_control_receiving_current(child_receiver);
    gir_control_owner_extend(binding, child);
    gir_control_require(gir_control_node(child)->parent == ((gir_control_owner *)binding)->boundary);
    gir_control_receiving_open(child);
    child = gir_control_receiving_renew(child_receiver);
    stack.top++;
    ((gir_control_metadata *)child)->count = 1;
    if (outcome == 0) {
        uint8_t *nested = gir_control_receiving_open(child);
        uint8_t *certificate = gir_control_receiving_cancel(nested, 0, NULL);
        gir_control_require(((gir_control_owner *)binding)->boundary->progress == GIR_CONTROL_SUSPENDED);
        gir_control_attempt_cancel(certificate);
        certificate = gir_control_receiving_cancel(child_receiver, 0, NULL);
        gir_control_attempt_cancel(certificate);
        gir_control_require(stack.top == bytes + 1 && header.len == 1);
    } else if (outcome == 1) {
        gir_control_attempt_finish(child);
        header.len = 2;
        gir_control_owner_update(binding, header.len, stack.top);
        gir_control_require(((gir_control_owner *)binding)->boundary->write_end == bytes + 2);
        gir_control_attempt_publish(child);
    } else if (outcome == 3) {
        uint8_t *ticket = gir_control_exit_reserve(child_receiver, 0, NULL);
        uint8_t *replacement = gir_control_exit_selected(ticket);
        stack.top++;
        ((gir_control_metadata *)replacement)->count = 1;
        gir_control_attempt_finish(replacement);
        uint8_t *carried[] = {replacement};
        uint8_t *certificate = gir_control_receiving_cancel(child_receiver, 1, carried);
        gir_control_require(((gir_control_owner *)binding)->boundary->progress == GIR_CONTROL_SUSPENDED);
        uint8_t *start = gir_control_exit_prepare(ticket, replacement);
        memmove(start, gir_control_attempt_start(replacement), 1);
        stack.top = start + 1;
        gir_control_exit_commit(ticket, replacement, start);
        gir_control_exit_release(ticket);
        gir_control_attempt_cancel(certificate);
        header.len = 2;
        gir_control_owner_update(binding, header.len, stack.top);
        gir_control_attempt_publish(replacement);
    } else if (outcome == 4) {
        uint8_t *ticket = gir_control_exit_reserve(receiver, 1, binding);
        gir_control_exit_mark_named(ticket);
        gir_control_exit_discard(ticket, 0, NULL);
        gir_control_require(stack.top == bytes + 2 && gir_control_node(child)->progress == GIR_CONTROL_OPEN);
        gir_control_require(((gir_control_owner *)binding)->boundary->progress == GIR_CONTROL_SUSPENDED);
        gir_control_attempt_finish(child);
        header.len = 2;
        gir_control_owner_update(binding, header.len, stack.top);
        gir_control_attempt_publish(child);
    } else {
        uint8_t *ticket = gir_control_exit_reserve(receiver, 1, binding);
        gir_control_exit_mark_named(ticket);
        gir_control_require(stack.top == bytes + 2);
        raw = gir_control_exit_selected(ticket);
        gir_control_require(stack.top == bytes + 1 && header.len == 1);
        gir_control_require(gir_control_node(child)->progress == GIR_CONTROL_ABANDONED);
        uint8_t *start = gir_control_exit_prepare(ticket, raw);
        gir_control_exit_commit(ticket, raw, start);
        gir_control_exit_release(ticket);
        gir_control_attempt_return(raw);
    }
    gir_control_owner_check(binding);
    gir_control_require(((gir_control_owner *)binding)->boundary->progress == GIR_CONTROL_BUILT);
    gir_control_leave(scope);
}
static void cancelled_owner_extensions(void) {
    uint8_t bytes[128] = {0};
    gs_stack stack = {0};
    stack.top = bytes;
    uint8_t *scope = gir_control_enter();
    uint8_t *receiver = gir_control_receiving_new((uint8_t *)&stack, bytes, 121, 0);
    uint8_t *raw = gir_control_receiving_current(receiver);
    gir_control_receiving_open(raw);
    raw = gir_control_receiving_renew(receiver);
    stack.top++;
    ((gir_control_metadata *)raw)->count = 1;
    gir_control_attempt_finish(raw);
    gir_hdr header = {bytes, 1};
    uint8_t *binding = gir_control_owner_bind(receiver, (uint8_t *)&header, (uint8_t *)&stack);
    gir_control_attempt_return(raw);
    for (int retry = 0; retry < 1000; retry++) {
        uint8_t *child_receiver = gir_control_receiving_new((uint8_t *)&stack, stack.top, retry, 0);
        uint8_t *child = gir_control_receiving_current(child_receiver);
        gir_control_owner_extend(binding, child);
        gir_control_receiving_open(child);
        child = gir_control_receiving_renew(child_receiver);
        stack.top++;
        ((gir_control_metadata *)child)->count = 1;
        uint8_t *certificate = gir_control_receiving_cancel(child_receiver, 0, NULL);
        gir_control_attempt_cancel(certificate);
        gir_control_require(gir_control_scope_top->leases == NULL);
        gir_control_require(gir_control_scope_top->receivers->next == NULL);
        gir_control_require(gir_control_live_attempts == ((gir_control_owner *)binding)->boundary);
        gir_control_require(gir_control_live_attempts->live_next == NULL);
    }
    gir_control_leave(scope);
}
static void owner_target_handoff(void) {
    uint8_t bytes[128] = {0};
    gs_stack stack = {0};
    stack.top = bytes;
    uint8_t *scope = gir_control_enter();
    uint8_t *receiver = gir_control_receiving_new((uint8_t *)&stack, bytes, 131, 0);
    uint8_t *raw = gir_control_receiving_current(receiver);
    gir_control_receiving_open(raw);
    raw = gir_control_receiving_renew(receiver);
    stack.top++;
    ((gir_control_metadata *)raw)->count = 1;
    gir_control_attempt_finish(raw);
    gir_hdr header = {bytes, 1};
    uint8_t *binding = gir_control_owner_bind(receiver, (uint8_t *)&header, (uint8_t *)&stack);
    gir_control_attempt_return(raw);
    for (int retry = 0; retry < 1000; retry++) {
        uint8_t *absent[] = {NULL, NULL};
        uint8_t *call = gir_control_call_push(0, NULL, 2, absent);
        uint8_t *callee = gir_control_enter();
        int64_t positions[] = {1};
        uint8_t *target = gir_control_owner_target_enter(0, 1, positions);
        uint8_t *arguments[] = {binding, NULL};
        uint8_t *inner = gir_control_call_push(0, NULL, 2, arguments);
        uint8_t *helper = gir_control_enter();
        uint8_t *borrowed = gir_control_owner_param(1);
        gir_control_owner_target_result(borrowed, 0, 0);
        gir_control_leave(helper);
        gir_control_call_pop(inner);
        gir_control_require(gir_control_owner_target_get(target, 0) == binding);
        gir_control_owner_target_leave(target);
        gir_control_leave(callee);
        gir_control_require(gir_control_owner_get(call, 1) == binding);
        gir_control_call_pop(call);
        gir_control_require(gir_control_owner_targets[0] == NULL && gir_control_scope_top->owners->next == NULL);
    }
    gir_control_owner_check(binding);
    gir_control_leave(scope);
}
static void borrowed_target_cancellation(void) {
    uint8_t bytes[128] = {0};
    gs_stack stack = {0};
    stack.top = bytes;
    uint8_t *scope = gir_control_enter();
    uint8_t *receiver = gir_control_receiving_new((uint8_t *)&stack, bytes, 141, 0);
    uint8_t *raw = gir_control_receiving_current(receiver);
    gir_control_receiving_open(raw);
    raw = gir_control_receiving_renew(receiver);
    stack.top++;
    ((gir_control_metadata *)raw)->count = 1;
    gir_control_attempt_finish(raw);
    uint8_t *binding = gir_control_named_bind(raw);
    gir_control_attempt_return(raw);
    uint8_t *outer_ticket = gir_control_exit_reserve(receiver, 1, binding);
    uint8_t *helper = gir_control_enter();
    gir_control_receiving_drop(receiver);
    raw = gir_control_receiving_current(receiver);
    uint8_t *carried[] = {raw};
    uint8_t *certificate = gir_control_receiving_cancel(receiver, 1, carried);
    gir_control_attempt_cancel(certificate);
    gir_control_require(((gir_control_receiving *)receiver)->scope == (gir_control_scope *)scope);
    gir_control_require(!((gir_control_receiving *)receiver)->consumed);
    gir_control_receiving_transfer(receiver, raw, 0);
    gir_control_attempt_return(raw);
    gir_control_leave(helper);
    gir_control_exit_discard(outer_ticket, 0, NULL);
    raw = gir_control_receiving_current(receiver);
    uint8_t *ticket = gir_control_exit_adopt(receiver, raw);
    uint8_t *start = gir_control_exit_prepare(ticket, raw);
    gir_control_exit_commit(ticket, raw, start);
    gir_control_exit_release(ticket);
    gir_control_attempt_publish(raw);
    gir_control_leave(scope);
}
static void waiting_calls(int built) {
    uint8_t bytes[128] = {0};
    gs_stack stack = {0};
    stack.top = bytes;
    uint8_t *caller = gir_control_enter();
    uint8_t *receiver = gir_control_receiving_new((uint8_t *)&stack, bytes, 71, 0);
    gir_control_attempt *attempt = ((gir_control_receiving *)receiver)->boundary;
    for (int iteration = 0; iteration < (built ? 1 : 1000); iteration++) {
        uint8_t *raw = gir_control_receiving_current(receiver);
        uint8_t *inputs[] = {raw};
        uint8_t *call = gir_control_call_push(1, inputs, 0, NULL);
        uint8_t *callee = gir_control_enter();
        uint8_t *incoming = gir_control_call_param(0);
        raw = gir_control_receiving_current(incoming);
        gir_control_receiving_open(raw);
        if (built) {
            raw = gir_control_receiving_renew(incoming);
            bytes[0] = 65;
            stack.top++;
            ((gir_control_metadata *)raw)->count = 1;
            gir_control_attempt_finish(raw);
            gir_control_named_bind(raw);
            gir_control_attempt_return(raw);
        }
        uint8_t *waiting = gir_control_exit_wait(incoming);
        gir_control_ticket *ticket = (gir_control_ticket *)waiting;
        gir_control_require(!ticket->selected && !ticket->snapshot_attempt && !ticket->boundary);
        gir_control_exit_discard(waiting, 0, NULL);
        raw = gir_control_receiving_cancel(incoming, 0, NULL);
        gir_control_require(attempt->progress == (built ? GIR_CONTROL_BUILT : GIR_CONTROL_OPEN));
        gir_control_require(attempt->metadata.count == built && stack.top == bytes + built);
        gir_control_attempt_cancel(raw);
        gir_control_leave(callee);
        raw = gir_control_call_get(call, 0);
        gir_control_require(gir_control_find_lease(raw)->cleanup == GIR_CONTROL_UNSELECTED_COMPLETION);
        gir_control_require(gir_control_find_lease(raw)->progress == GIR_CONTROL_CANCELLED);
        gir_control_attempt_cancel(raw);
        gir_control_call_pop(call);
        gir_control_require(node_count(attempt->graph) == 1 && !attempt->graph->tickets);
        gir_control_require(!gir_control_scope_top->leases && !gir_control_scope_top->tickets);
        gir_control_require(attempt->progress == (built ? GIR_CONTROL_BUILT : GIR_CONTROL_OPEN));
    }
    uint8_t *raw = gir_control_receiving_current(receiver);
    if (!built) gir_control_attempt_finish(raw);
    gir_control_attempt_publish(raw);
    gir_control_leave(caller);
}

static void waiting_selection(int named) {
    uint8_t bytes[128] = {0};
    gs_stack stack = {0};
    stack.top = bytes;
    uint8_t *scope = gir_control_enter();
    uint8_t *receiver = gir_control_receiving_new((uint8_t *)&stack, bytes, 73, 0);
    uint8_t *raw = gir_control_receiving_current(receiver);
    gir_control_receiving_open(raw);
    uint8_t *binding = NULL;
    if (named) {
        raw = gir_control_receiving_renew(receiver);
        bytes[0] = 65;
        stack.top++;
        ((gir_control_metadata *)raw)->count = 1;
        gir_control_attempt_finish(raw);
        binding = gir_control_named_bind(raw);
        gir_control_attempt_return(raw);
    }
    uint8_t *waiting = gir_control_exit_wait(receiver);
    gir_control_ticket *ticket = (gir_control_ticket *)waiting;
    gir_control_exit_select(waiting, (uint8_t)named, binding);
    gir_control_require(ticket == ticket->graph->tickets && ticket->selected == ((gir_control_receiving *)receiver)->boundary);
    if (named) gir_control_exit_mark_named(waiting);
    raw = gir_control_exit_selected(waiting);
    if (!named) gir_control_attempt_finish(raw);
    uint8_t *start = gir_control_exit_prepare(waiting, raw);
    gir_control_exit_commit(waiting, raw, start);
    gir_control_exit_release(waiting);
    gir_control_attempt_publish(raw);
    gir_control_leave(scope);
}

static void waiting_terminal_release(void) {
    uint8_t bytes[128] = {0};
    gs_stack stack = {0};
    stack.top = bytes;
    uint8_t *scope = gir_control_enter();
    uint8_t *receiver = gir_control_receiving_new((uint8_t *)&stack, bytes, 79, 0);
    uint8_t *raw = gir_control_receiving_current(receiver);
    gir_control_receiving_open(raw);
    gir_control_attempt *attempt = ((gir_control_receiving *)receiver)->boundary;
    uint8_t *waiting = gir_control_exit_wait(receiver);
    gir_control_exit_release(waiting);
    gir_control_require(attempt->progress == GIR_CONTROL_OPEN && stack.top == bytes);
    gir_control_require(!((gir_control_receiving *)receiver)->unselected && !attempt->graph->tickets);
    gir_control_leave(scope);
}

static void waiting_supersession(void) {
    uint8_t bytes[128] = {0};
    gs_stack stack = {0};
    stack.top = bytes;
    uint8_t *scope = gir_control_enter();
    uint8_t *receiver = gir_control_receiving_new((uint8_t *)&stack, bytes, 81, 0);
    uint8_t *raw = gir_control_receiving_current(receiver);
    gir_control_receiving_open(raw);
    uint8_t *waiting = gir_control_exit_wait(receiver);
    uint8_t *selected = gir_control_exit_reserve(receiver, 0, NULL);
    raw = gir_control_exit_selected(selected);
    bytes[0] = 65;
    stack.top++;
    ((gir_control_metadata *)raw)->count = 1;
    gir_control_attempt_finish(raw);
    uint8_t *carried[] = {raw};
    gir_control_exit_discard(waiting, 1, carried);
    uint8_t *cancelled = gir_control_receiving_cancel(receiver, 1, carried);
    gir_control_require(gir_control_find_lease(cancelled)->cleanup != GIR_CONTROL_UNSELECTED_COMPLETION);
    gir_control_attempt_cancel(cancelled);
    uint8_t *start = gir_control_exit_prepare(selected, raw);
    gir_control_exit_commit(selected, raw, start);
    gir_control_exit_release(selected);
    gir_control_require(gir_control_node(raw)->progress == GIR_CONTROL_BUILT && stack.top == bytes + 1);
    gir_control_attempt_publish(raw);
    gir_control_leave(scope);
}

static void cancellation_without_wait(int written) {
    uint8_t bytes[128] = {0};
    gs_stack stack = {0};
    stack.top = bytes;
    uint8_t *scope = gir_control_enter();
    uint8_t *receiver = gir_control_receiving_new((uint8_t *)&stack, bytes, 83, 0);
    uint8_t *raw = gir_control_receiving_current(receiver);
    gir_control_receiving_open(raw);
    raw = gir_control_receiving_renew(receiver);
    if (written) {
        bytes[0] = 65;
        stack.top++;
        ((gir_control_metadata *)raw)->count = 1;
    }
    raw = gir_control_receiving_cancel(receiver, 0, NULL);
    gir_control_require(gir_control_node(raw)->progress == GIR_CONTROL_ABANDONED && stack.top == bytes);
    gir_control_require(gir_control_find_lease(raw)->cleanup != GIR_CONTROL_UNSELECTED_COMPLETION);
    gir_control_attempt_cancel(raw);
    gir_control_leave(scope);
}

static void waiting_rejection(int kind) {
    uint8_t bytes[128] = {0};
    gs_stack stack = {0};
    stack.top = bytes;
    gir_control_enter();
    uint8_t *receiver = gir_control_receiving_new((uint8_t *)&stack, bytes, 89, 0);
    uint8_t *raw = gir_control_receiving_current(receiver);
    gir_control_receiving_open(raw);
    if (kind == 10) {
        raw = gir_control_receiving_renew(receiver);
        gir_control_attempt_finish(raw);
    }
    if (kind == 6) gir_control_enter();
    uint8_t *waiting = gir_control_exit_wait(receiver);
    switch (kind) {
        case 1:
            gir_control_exit_select(waiting, 0, NULL);
            gir_control_exit_select(waiting, 0, NULL);
            break;
        case 2: gir_control_exit_selected(waiting); break;
        case 3: gir_control_receiving_renew(receiver); break;
        case 4: gir_control_receiving_drop(receiver); break;
        case 5:
            gir_control_exit_discard(waiting, 0, NULL);
            gir_control_exit_select(waiting, 0, NULL);
            break;
        case 7:
            gir_control_exit_reserve(receiver, 0, NULL);
            gir_control_exit_discard(waiting, 0, NULL);
            gir_control_receiving_cancel(receiver, 0, NULL);
            break;
        case 8: {
            uint8_t *selected = gir_control_exit_reserve(receiver, 0, NULL);
            raw = gir_control_exit_selected(selected);
            uint8_t *carried[] = {raw};
            gir_control_exit_discard(waiting, 1, carried);
            gir_control_receiving_cancel(receiver, 1, carried);
            break;
        }
        case 9: {
            gir_control_exit_discard(waiting, 0, NULL);
            raw = gir_control_receiving_current(receiver);
            uint8_t *carried[] = {raw};
            gir_control_receiving_cancel(receiver, 1, carried);
            break;
        }
        case 10: {
            uint8_t *carried[] = {raw};
            gir_control_exit_discard(waiting, 1, carried);
            gir_control_receiving_cancel(receiver, 1, carried);
            break;
        }
    }
    exit(99);
}

static void physical_layout(int backing_prefix, int local_prefix) {
    uint8_t bytes[128] = {0};
    gs_stack stack = {0};
    stack.top = bytes;
    uint8_t *scope = gir_control_enter();
    uint8_t *receiver = gir_control_receiving_new((uint8_t *)&stack, bytes, 171, backing_prefix);
    uint8_t *raw = gir_control_receiving_current(receiver);
    stack.top += backing_prefix;
    gir_control_receiving_open(raw);
    raw = gir_control_receiving_renew(receiver);
    gir_control_attempt_prepare_named(raw, local_prefix);
    int prefix = backing_prefix || local_prefix ? 4 : 0;
    gir_control_require(gir_control_attempt_prefix(raw) == prefix);
    *stack.top++ = 65;
    ((gir_control_metadata *)raw)->count = 1;
    if (prefix) { uint32_t count = 1; memcpy(bytes, &count, 4); }
    gir_control_attempt_finish(raw);
    gir_control_attempt_normalize(raw);
    gir_control_require(gir_control_attempt_prefix(raw) == backing_prefix &&
        stack.top == bytes + backing_prefix + 1 && bytes[backing_prefix] == 65);
    gir_control_attempt_publish(raw);
    gir_control_leave(scope);
    gir_control_require(gir_control_live_attempts == NULL);
}

static void explicit_prefix_adapters(void) {
    uint8_t bytes[128] = {0};
    gs_stack stack = {0};
    stack.top = bytes;
    uint8_t *scope = gir_control_enter();
    uint8_t *receiver = gir_control_receiving_new((uint8_t *)&stack, bytes, 175, 0);
    uint8_t *raw = gir_control_receiving_current(receiver);
    gir_control_attempt_pack(raw);
    gir_control_require(gir_control_attempt_prefix(raw) == 4 && stack.top == bytes + 4);
    *stack.top++ = 65;
    ((gir_control_metadata *)raw)->count = 1;
    gir_control_attempt_finish(raw);
    gir_control_attempt_remove_header(raw);
    gir_control_require(gir_control_attempt_prefix(raw) == 0 && stack.top == bytes + 1 && bytes[0] == 65);
    gir_control_attempt_normalize(raw);
    gir_control_attempt_publish(raw);
    gir_control_leave(scope);
}

static void immutable_named_views(void) {
    uint8_t bytes[128] = {0};
    gs_stack stack = {0};
    stack.top = bytes;
    uint8_t *scope = gir_control_enter();
    uint8_t *receiver = gir_control_receiving_new((uint8_t *)&stack, bytes, 191, 0);
    uint8_t *raw = gir_control_receiving_current(receiver);
    gir_control_attempt_pack(raw);
    *stack.top++ = 65;
    ((gir_control_metadata *)raw)->count = 1;
    gir_control_attempt_finish(raw);
    uint8_t *binding = gir_control_named_bind(raw);
    gir_control_require(gir_control_owner_is_named(binding) && !gir_control_owner_is_named(NULL));
    gir_control_require(gir_control_named_base(binding, bytes) == bytes + 4 && gir_control_named_count(binding, bytes) == 1);
    gir_control_attempt_remove_header(raw);
    gir_control_require(gir_control_named_base(binding, bytes) == bytes && gir_control_named_count(binding, bytes) == 1);
    gir_control_require(*gir_control_named_base(binding, bytes) == 65);
    gir_control_attempt_publish(raw);
    gir_control_leave(scope);
}

static void waiting_rearms(void) {
    uint8_t bytes[128] = {0};
    gs_stack stack = {0};
    stack.top = bytes;
    uint8_t *scope = gir_control_enter();
    uint8_t *receiver = gir_control_receiving_new((uint8_t *)&stack, bytes, 211, 0);
    gir_control_receiving_open(gir_control_receiving_current(receiver));
    uint8_t *token = gir_control_exit_wait(receiver);
    gir_control_ticket *ticket = (gir_control_ticket *)token;
    for (int retry = 0; retry < 1000; retry++) {
        gir_control_exit_select(token, 0, NULL);
        uint8_t *guard = gir_control_receiving_open(gir_control_exit_selected(token));
        uint8_t *raw = gir_control_receiving_renew(guard);
        *stack.top++ = 65;
        ((gir_control_metadata *)raw)->count = 1;
        uint8_t *cancelled = gir_control_receiving_cancel(guard, 0, NULL);
        gir_control_attempt_cancel(cancelled);
        gir_control_exit_rearm(token);
        gir_control_require(ticket->role == GIR_CONTROL_WAITING && ticket->selected == NULL &&
            ticket->snapshot_attempt == NULL && !((gir_control_receiving *)receiver)->unselected &&
            ticket->graph->tickets == ticket && !ticket->previous && !ticket->scope_next &&
            gir_control_scope_top->tickets == ticket && !gir_control_scope_top->leases &&
            gir_control_scope_top->receivers == (gir_control_receiving *)receiver &&
            !((gir_control_receiving *)receiver)->next && node_count(ticket->graph) <= 2 && stack.top == bytes);
    }
    gir_control_exit_select(token, 0, NULL);
    uint8_t *raw = gir_control_exit_selected(token);
    *stack.top++ = 67;
    ((gir_control_metadata *)raw)->count = 1;
    gir_control_attempt_finish(raw);
    uint8_t *start = gir_control_exit_prepare(token, raw);
    gir_control_exit_commit(token, raw, start);
    gir_control_exit_release(token);
    gir_control_attempt_publish(raw);
    gir_control_leave(scope);
}

static void named_waiting_rearms(void) {
    uint8_t bytes[128] = {0};
    gs_stack stack = {0};
    stack.top = bytes;
    uint8_t *scope = gir_control_enter();
    uint8_t *receiver = gir_control_receiving_new((uint8_t *)&stack, bytes, 213, 0);
    gir_control_receiving_open(gir_control_receiving_current(receiver));
    uint8_t *raw = gir_control_receiving_renew(receiver);
    *stack.top++ = 65;
    ((gir_control_metadata *)raw)->count = 1;
    gir_control_attempt_finish(raw);
    uint8_t *binding = gir_control_named_bind(raw);
    gir_control_attempt_return(raw);
    size_t references = ((gir_control_owner *)binding)->references;
    uint8_t *token = gir_control_exit_wait(receiver);
    for (int ready = 0; ready < 2; ready++) {
        gir_control_exit_select(token, 1, binding);
        if (ready) gir_control_exit_mark_named(token);
        gir_control_exit_rearm(token);
        gir_control_require(((gir_control_owner *)binding)->references == references &&
            ((gir_control_receiving *)receiver)->boundary->progress == GIR_CONTROL_BUILT &&
            ((gir_control_receiving *)receiver)->boundary->metadata.count == 1 &&
            bytes[0] == 65 && stack.top == bytes + 1);
    }
    gir_control_exit_select(token, 1, binding);
    gir_control_exit_mark_named(token);
    raw = gir_control_exit_selected(token);
    uint8_t *start = gir_control_exit_prepare(token, raw);
    gir_control_exit_commit(token, raw, start);
    gir_control_exit_release(token);
    gir_control_attempt_publish(raw);
    gir_control_leave(scope);
}

static void rearm_rejection(int kind) {
    uint8_t bytes[128] = {0};
    gs_stack stack = {0};
    stack.top = bytes;
    gir_control_enter();
    uint8_t *receiver = gir_control_receiving_new((uint8_t *)&stack, bytes, 217, 0);
    gir_control_receiving_open(gir_control_receiving_current(receiver));
    uint8_t *token = kind == 1 ? gir_control_exit_reserve(receiver, 0, NULL) : gir_control_exit_wait(receiver);
    if (kind == 1 || kind == 2) gir_control_exit_rearm(token);
    if (kind == 8) {
        gir_control_exit_discard(token, 0, NULL);
        gir_control_exit_rearm(token);
    }
    gir_control_exit_select(token, 0, NULL);
    if (kind == 9) {
        gir_control_exit_rearm(token);
        gir_control_exit_rearm(token);
    }
    if (kind == 7) {
        gir_control_enter();
        gir_control_exit_rearm(token);
    }
    uint8_t *raw = gir_control_exit_selected(token);
    if (kind == 3) gir_control_exit_rearm(token);
    if (kind == 6) {
        uint8_t *inputs[] = {raw};
        gir_control_call_push(1, inputs, 0, NULL);
        gir_control_drop_lease(raw);
        gir_control_exit_rearm(token);
    }
    gir_control_attempt_finish(raw);
    if (kind == 4) gir_control_exit_rearm(token);
    if (kind == 5) {
        gir_control_exit_release(token);
        gir_control_receiving_transfer(receiver, raw, 0);
        token = gir_control_exit_adopt(receiver, raw);
        gir_control_attempt_return(raw);
        gir_control_exit_rearm(token);
    }
    if (kind == 10) {
        gir_control_exit_prepare(token, raw);
        gir_control_attempt_return(raw);
        gir_control_exit_rearm(token);
    }
    exit(99);
}

static void limited_staging(void) {
    uint8_t inline_bytes[5] = {239, 190, 190, 190, 239};
    uint8_t scratch_bytes[16] = {0};
    gs_stack inline_cursor = { inline_bytes + 1 };
    gs_stack scratch = { scratch_bytes };
    uint8_t *scope = gir_control_enter();
    uint8_t *receiver = gir_control_receiving_new((uint8_t *)&inline_cursor, inline_bytes + 1, 223, 0);
    uint8_t *raw = gir_control_attempt_stage(gir_control_receiving_current(receiver), (uint8_t *)&scratch,
        inline_bytes + 4, 3, 1);
    gir_control_require(inline_cursor.top == inline_bytes + 1 && inline_bytes[1] == 190 &&
        gir_control_node(raw)->metadata.identity == 223 && gir_control_node(raw)->stack == &scratch);
    uint8_t *inputs[] = {raw};
    uint8_t *call = gir_control_call_push(1, inputs, 0, NULL);
    uint8_t *callee = gir_control_enter();
    uint8_t *incoming = gir_control_call_param(0);
    raw = gir_control_receiving_current(incoming);
    gir_control_require(gir_control_receiving_open(raw) == incoming);
    raw = gir_control_receiving_current(incoming);
    *scratch.top++ = 65;
    *scratch.top++ = 66;
    ((gir_control_metadata *)raw)->count = 2;
    gir_control_attempt_finish(raw);
    gir_control_attempt_return(raw);
    gir_control_leave(callee);
    raw = gir_control_call_get(call, 0);
    gir_control_call_pop(call);
    gir_control_require(gir_control_node(raw)->staging.cursor == &inline_cursor);
    gir_control_receiving_drop(receiver);
    raw = gir_control_attempt_fit(raw, (uint8_t *)&inline_cursor);
    gir_control_require(inline_bytes[0] == 239 && inline_bytes[1] == 65 && inline_bytes[2] == 66 &&
        inline_bytes[3] == 190 && inline_bytes[4] == 239 && inline_cursor.top == inline_bytes + 3 &&
        scratch.top == scratch_bytes && gir_control_node(raw)->metadata.identity == 223 &&
        !gir_control_node(raw)->staging.cursor && ((gir_control_metadata *)raw)->count == 2);
    gir_control_attempt_publish(raw);
    gir_control_leave(scope);
}

static void limited_staging_renewal(void) {
    uint8_t inline_bytes[3] = {190, 190, 239};
    uint8_t scratch_bytes[16] = {0};
    gs_stack inline_cursor = { inline_bytes };
    gs_stack scratch = { scratch_bytes };
    uint8_t *scope = gir_control_enter();
    uint8_t *receiver = gir_control_receiving_new((uint8_t *)&inline_cursor, inline_bytes, 229, 0);
    uint8_t *raw = gir_control_attempt_stage(gir_control_receiving_current(receiver), (uint8_t *)&scratch,
        inline_bytes + 2, 2, 1);
    receiver = gir_control_receiving_open(raw);
    uint8_t *ticket = gir_control_exit_wait(receiver);
    for (int retry = 0; retry < 1000; retry++) {
        gir_control_exit_select(ticket, 0, NULL);
        uint8_t *guard = gir_control_receiving_open(gir_control_exit_selected(ticket));
        raw = gir_control_receiving_renew(guard);
        *scratch.top++ = 65;
        ((gir_control_metadata *)raw)->count = 1;
        gir_control_attempt_cancel(gir_control_receiving_cancel(guard, 0, NULL));
        gir_control_exit_rearm(ticket);
        gir_control_require(scratch.top == scratch_bytes && inline_cursor.top == inline_bytes &&
            inline_bytes[0] == 190 && inline_bytes[1] == 190 && node_count(((gir_control_receiving *)receiver)->graph) <= 2);
    }
    gir_control_exit_select(ticket, 0, NULL);
    raw = gir_control_exit_selected(ticket);
    *scratch.top++ = 67;
    ((gir_control_metadata *)raw)->count = 1;
    gir_control_attempt_finish(raw);
    uint8_t *start = gir_control_exit_prepare(ticket, raw);
    gir_control_exit_commit(ticket, raw, start);
    gir_control_exit_release(ticket);
    gir_control_receiving_drop(receiver);
    raw = gir_control_attempt_fit(raw, (uint8_t *)&inline_cursor);
    gir_control_require(inline_bytes[0] == 67 && inline_bytes[1] == 190 && inline_bytes[2] == 239 &&
        scratch.top == scratch_bytes && inline_cursor.top == inline_bytes + 1);
    gir_control_attempt_publish(raw);
    gir_control_leave(scope);
}

static void limited_staging_replacement(void) {
    uint8_t inline_bytes[3] = {190, 190, 239};
    uint8_t scratch_bytes[16] = {0};
    gs_stack inline_cursor = { inline_bytes };
    gs_stack scratch = { scratch_bytes };
    uint8_t *scope = gir_control_enter();
    uint8_t *receiver = gir_control_receiving_new((uint8_t *)&inline_cursor, inline_bytes, 233, 0);
    uint8_t *raw = gir_control_attempt_stage(gir_control_receiving_current(receiver), (uint8_t *)&scratch,
        inline_bytes + 2, 2, 1);
    receiver = gir_control_receiving_open(raw);
    raw = gir_control_receiving_renew(receiver);
    *scratch.top++ = 65;
    ((gir_control_metadata *)raw)->count = 1;
    gir_control_attempt_finish(raw);
    gir_control_attempt_return(raw);
    uint8_t *ticket = gir_control_exit_reserve(receiver, 0, NULL);
    raw = gir_control_exit_selected(ticket);
    *scratch.top++ = 66;
    ((gir_control_metadata *)raw)->count = 1;
    gir_control_attempt_finish(raw);
    uint8_t *carried[] = {raw};
    gir_control_attempt_cancel(gir_control_receiving_cancel(receiver, 1, carried));
    uint8_t *start = gir_control_exit_prepare(ticket, raw);
    memmove(start, gir_control_find_lease(raw)->start, 1);
    scratch.top = start + 1;
    gir_control_exit_commit(ticket, raw, start);
    gir_control_exit_release(ticket);
    raw = gir_control_attempt_fit(raw, (uint8_t *)&inline_cursor);
    gir_control_require(inline_bytes[0] == 66 && inline_bytes[1] == 190 && inline_bytes[2] == 239 &&
        scratch.top == scratch_bytes && inline_cursor.top == inline_bytes + 1);
    gir_control_attempt_publish(raw);
    gir_control_leave(scope);
}

static void limited_staging_distinct(void) {
    uint8_t inline_bytes[2][3] = {{190, 190, 239}, {190, 190, 239}};
    uint8_t scratch_bytes[2][8] = {{0}, {0}};
    gs_stack inline_cursor[2] = {{inline_bytes[0]}, {inline_bytes[1]}};
    gs_stack scratch[2] = {{scratch_bytes[0]}, {scratch_bytes[1]}};
    uint8_t *scope = gir_control_enter();
    uint8_t *raw[2];
    for (int index = 0; index < 2; index++) {
        uint8_t *receiver = gir_control_receiving_new((uint8_t *)&inline_cursor[index], inline_bytes[index], 233 + index, 0);
        raw[index] = gir_control_attempt_stage(gir_control_receiving_current(receiver), (uint8_t *)&scratch[index],
            inline_bytes[index] + 2, 2, 1);
    }
    for (int index = 0; index < 2; index++) {
        *scratch[index].top++ = (uint8_t)(65 + index);
        ((gir_control_metadata *)raw[index])->count = 1;
        gir_control_attempt_finish(raw[index]);
        raw[index] = gir_control_attempt_fit(raw[index], (uint8_t *)&inline_cursor[index]);
        gir_control_require(inline_bytes[index][0] == 65 + index && inline_bytes[index][1] == 190 && inline_bytes[index][2] == 239);
        gir_control_attempt_publish(raw[index]);
    }
    gir_control_leave(scope);
}

static void limited_staging_rejection(int kind) {
    uint8_t inline_bytes[16] = {0};
    uint8_t scratch_bytes[16] = {0};
    gs_stack inline_cursor = { inline_bytes };
    gs_stack scratch = { scratch_bytes };
    gir_control_enter();
    uint8_t *receiver = gir_control_receiving_new((uint8_t *)&inline_cursor, inline_bytes, 227, 0);
    uint8_t *raw = gir_control_receiving_current(receiver);
    if (kind == 1) {
        receiver = gir_control_receiving_open(raw);
        raw = gir_control_receiving_renew(receiver);
    }
    if (kind == 2) gir_control_exit_wait(receiver);
    if (kind == 18) gir_control_receiving_new((uint8_t *)&scratch, scratch.top, 237, 0);
    if (kind == 19) {
        uint8_t other_inline[3] = {0};
        gs_stack other_cursor = {other_inline};
        uint8_t *other = gir_control_receiving_new((uint8_t *)&other_cursor, other_inline, 239, 0);
        gir_control_attempt_stage(gir_control_receiving_current(other), (uint8_t *)&scratch, other_inline + 3, 3, 1);
    }
    if (kind == 3) ((gir_control_metadata *)raw)->count = 1;
    if (kind == 14) gir_control_find_lease(raw)->prefix = 4;
    raw = gir_control_attempt_stage(raw, kind == 6 ? (uint8_t *)&inline_cursor : (uint8_t *)&scratch,
        inline_bytes + (kind == 4 ? 2 : 3), kind == 13 ? INT64_MAX : 3,
        kind == 5 ? 0 : (kind == 13 ? 2 : 1));
    uint8_t *parent = NULL;
    if (kind == 17) {
        uint8_t *parent_receiver = gir_control_receiving_new((uint8_t *)&scratch, scratch.top, 229, 0);
        parent = gir_control_receiving_current(parent_receiver);
        gir_control_attempt_child(parent, raw);
    }
    if (kind == 7) gir_control_attempt_fit(raw, (uint8_t *)&inline_cursor);
    int count = kind == 8 ? 4 : 2;
    for (int index = 0; index < count; index++) *scratch.top++ = 65;
    ((gir_control_metadata *)raw)->count = kind == 10 ? 1 : count;
    gir_control_attempt_finish(raw);
    if (kind == 17) gir_control_attempt_attach(parent, raw);
    if (kind == 15) gir_control_attempt_publish(raw);
    if (kind == 16) gir_control_receiving_transfer(receiver, raw, 0);
    if (kind == 11) scratch.top++;
    if (kind == 12) inline_cursor.top++;
    gs_stack wrong = { inline_bytes };
    gir_control_attempt_fit(raw, kind == 9 ? (uint8_t *)&wrong : (uint8_t *)&inline_cursor);
    exit(99);
}

static void physical_rejection(int kind) {
    uint8_t bytes[128] = {0};
    gs_stack stack = {0};
    stack.top = bytes;
    uint8_t *scope = gir_control_enter();
    uint8_t *receiver = gir_control_receiving_new((uint8_t *)&stack, bytes, 181, 0);
    uint8_t *raw = gir_control_receiving_current(receiver);
    switch (kind) {
        case 1:
            *stack.top++ = 65;
            ((gir_control_metadata *)raw)->count = 1;
            gir_control_attempt_prepare_named(raw, 4);
            break;
        case 2: gir_control_attempt_prepare_named(raw, 2); break;
        case 3: gir_control_attempt_normalize(raw); break;
        case 4:
            raw = gir_control_receiving_cancel(receiver, 0, NULL);
            gir_control_attempt_normalize(raw);
            break;
        case 5:
            gir_control_attempt_prepare_named(raw, 4);
            *stack.top++ = 65;
            ((gir_control_metadata *)raw)->count = 1;
            gir_control_attempt_finish(raw);
            stack.top++;
            gir_control_attempt_normalize(raw);
            break;
        case 6:
            gir_control_drop_lease(raw);
            gir_control_enter();
            raw = gir_control_receiving_current(receiver);
            gir_control_attempt_prepare_named(raw, 4);
            break;
        case 7:
            *stack.top++ = 65;
            ((gir_control_metadata *)raw)->count = 1;
            gir_control_attempt_finish(raw);
            gir_control_attempt_return(raw);
            gir_control_attempt_normalize(raw);
            break;
        case 8:
            *stack.top++ = 65;
            ((gir_control_metadata *)raw)->count = 1;
            gir_control_attempt_pack(raw);
            break;
        case 9:
            gir_control_attempt_pack(raw);
            gir_control_attempt_pack(raw);
            break;
        case 10: gir_control_attempt_remove_header(raw); break;
        case 11:
            *stack.top++ = 65;
            ((gir_control_metadata *)raw)->count = 1;
            gir_control_attempt_finish(raw);
            gir_control_attempt_remove_header(raw);
            break;
        case 12:
            gir_control_attempt_pack(raw);
            *stack.top++ = 65;
            ((gir_control_metadata *)raw)->count = 1;
            gir_control_attempt_finish(raw);
            stack.top++;
            gir_control_attempt_remove_header(raw);
            break;
        case 13:
            gir_control_attempt_return(raw);
            gir_control_attempt_prefix(raw);
            break;
        case 14: gir_control_named_base(NULL, bytes); break;
        case 15:
        case 16:
        case 17: {
            *stack.top++ = 65;
            ((gir_control_metadata *)raw)->count = 1;
            gir_control_attempt_finish(raw);
            uint8_t *binding = gir_control_named_bind(raw);
            if (kind == 15) gir_control_named_base(binding, bytes + 1);
            if (kind == 16) gir_control_named_count(binding, bytes + 32);
            raw = gir_control_receiving_cancel(receiver, 0, NULL);
            gir_control_named_count(binding, bytes);
            break;
        }
    }
    (void)scope;
    exit(99);
}

int main(int argc, char **argv) {
    if (argc == 2) {
        int kind = atoi(argv[1]);
        if (kind <= 10) waiting_rejection(kind);
        else if (kind <= 27) physical_rejection(kind - 10);
        else if (kind <= 37) rearm_rejection(kind - 27);
        else limited_staging_rejection(kind - 37);
    }
    normal_call(); cancelled_retries(); bounded_call(); target_handoff(); completed_aliases(); named_owner_bindings();
    cancellation_certificate(); historical_named_source(); displaced_child_cleanup();
    for (int outcome = 0; outcome < 5; outcome++) owner_extension(outcome);
    cancelled_owner_extensions(); owner_target_handoff(); borrowed_target_cancellation();
    waiting_calls(0); waiting_calls(1); waiting_selection(0); waiting_selection(1);
    waiting_terminal_release(); waiting_supersession(); cancellation_without_wait(0); cancellation_without_wait(1);
    physical_layout(0, 0); physical_layout(0, 4); physical_layout(4, 0); physical_layout(4, 4);
    explicit_prefix_adapters(); immutable_named_views(); waiting_rearms(); named_waiting_rearms(); limited_staging_distinct(); limited_staging(); limited_staging_renewal(); limited_staging_replacement();
    gir_control_require(gir_control_live_attempts == NULL);
    return 0;
}
