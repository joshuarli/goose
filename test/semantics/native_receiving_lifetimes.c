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

int main(int argc, char **argv) {
    if (argc == 2) waiting_rejection(atoi(argv[1]));
    normal_call(); cancelled_retries(); bounded_call(); target_handoff(); completed_aliases(); named_owner_bindings();
    cancellation_certificate(); historical_named_source(); displaced_child_cleanup();
    for (int outcome = 0; outcome < 5; outcome++) owner_extension(outcome);
    cancelled_owner_extensions(); owner_target_handoff(); borrowed_target_cancellation();
    waiting_calls(0); waiting_calls(1); waiting_selection(0); waiting_selection(1);
    waiting_terminal_release(); waiting_supersession(); cancellation_without_wait(0); cancellation_without_wait(1);
    gir_control_require(gir_control_live_attempts == NULL);
    return 0;
}
