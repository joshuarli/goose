#pragma once

namespace goose {

class NodeVisits {
    vector<const Node *> slots;
    size_t count = 0;

    size_t Slot(const Node *node) const {
        auto bits = static_cast<uint64_t>(reinterpret_cast<uintptr_t>(node));
        bits ^= bits >> 33;
        bits *= UINT64_C(0xff51afd7ed558ccd);
        bits ^= bits >> 33;
        auto slot = static_cast<size_t>(bits) & (slots.size() - 1);
        while (slots[slot] && slots[slot] != node)
            slot = (slot + 1) & (slots.size() - 1);
        return slot;
    }

    void Grow() {
        auto previous = std::move(slots);
        slots.assign(previous.size() * 2, nullptr);
        for (auto node : previous)
            if (node) slots[Slot(node)] = node;
    }

public:
    bool Mark(const Node &node) {
        if (slots.empty()) slots.assign(64, nullptr);
        auto slot = Slot(&node);
        if (slots[slot]) return false;
        if (count == slots.size() / 2) {
            Grow();
            slot = Slot(&node);
        }
        slots[slot] = &node;
        count++;
        return true;
    }
};


}
