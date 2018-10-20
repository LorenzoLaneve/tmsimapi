//
// Non-deterministic Turing Machine Simulator
//
// Project for Algorithm and Data Structures (Politecnico di Milano, AY 2017/18)
//
// Copyright (c) 2018 Lorenzo Laneve
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of the GNU General Public License as published by the Free
// Software Foundation; either version 2 of the License, or (at your option)
// any later version.


//
// The project is single file because the testing system provided for software verification required me to do so.
//

#include <assert.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define STATE_TABLE_SLOTS       64      ///< Used slots for the states hash table. (NEEDS TO BE A POWER OF 2)
#define EDGE_TABLE_SLOTS        16      ///< Used slots for the edges hash table. (NEEDS TO BE A POWER OF 2) (Ignored if \c USE_HASH_AND_TREE is undefined)
#define FILEWRAPPER_BUFFER_SIZE 4096    ///< Buffer used to read input strings from the input file.
#define CELLS_PER_CHUNK         232     ///< Number of symbols held for each tape chunk.

//#define USE_HASH_AND_TREE             ///< If defined, uses the implementation with hash tables and red-black trees for transition graph edges. This implementation optimizes memory and is more flexible, but slightly slows down delta function computation.

#define RECYCLE_NOREF_CHUNKS            ///< If defined, chunks that are not used anymore will be put in a recycle list without being freed.
#define RECYCLE_END_CHUNKS              ///< If defined, chunks left at the end of a computation will be put in a recycle list without being freed.
#define RECYCLE_SOURCE_CHUNKS           ///< If defined, source chunks at the end of a computation will be put in a recycle list without being freed.
#define FAST_FORK                       ///< If defined, a "lazy" approach will be used for tape copying when a non-determinism is found.

#define GROUP_BITS 4                    ///< Defines how many bits of the symbols are used to address the list block. Please note that this is ignored if \c USE_HASH_AND_TREE is defined.
#define MOVE_LIST_SLOTS 256             ///< Defines how many different symbols need to be index for the list of transitions. Please note that this is ignored if \c USE_HASH_AND_TREE is defined.

#define SYMBOL_BLANK '_'                ///< The character value that is recognized as a "blank" symbol by the program.

#if defined(RECYCLE_NOREF_CHUNKS) || defined(RECYCLE_END_CHUNKS) || defined(RECYCLE_SOURCE_CHUNKS)
#define RECYCLE_CHUNKS
#endif

/*!
 \brief A non-null value if str starts with sub, \c NULL otherwise.
 */
#define strbeg(str, sub) (str == strstr(str, sub))
/*!
 \brief Returns a number to encode the specified move.
 */
#define moveToInt(move) ((move == 'L') ? 0 : ((move == 'R') ? 2 : 1))



/// UTIL: FILE WRAPPER

/*!
 \brief Structure used to optimise input file reading and reduce system calls.
 */
typedef struct {
    FILE *theFile;      ///< Pointer to the file to read.
    
    char *buffer;       ///< Buffer holding character read from the file.
    size_t bufptr;      ///< Pointer in the buffer to the next character that has to be read.
    size_t bufend;      ///< Pointer in the buffer to the last readable character.
} FileWrapper;

/*!
 \brief Reads the next character from the file buffer. If the buffer is empty, a new read from the file is attempted.
 \note Any \c EOF will be replaced by a line feed.
 */
char FileWrapper_getChar(FileWrapper *this_) {
    if (this_->bufptr >= this_->bufend) {
        // The buffer has been fully read and we need new data from the file.
        this_->bufend = fread(this_->buffer, sizeof(char), FILEWRAPPER_BUFFER_SIZE, this_->theFile);
        this_->bufptr = 0;
        
        if (!this_->bufend) {
            // If we haven't read anything it's because we're at the end of file.
            // Let's return the line feed to let the Turing Machine know that the input is over.
            return '\n';
        }
    } else if (this_->buffer[this_->bufptr] == '\r') { // Bugfix for CRLF left by Windows.
        this_->bufptr++;
        return FileWrapper_getChar(this_);
    }
    
    return this_->buffer[this_->bufptr++];
}

/*!
 \brief Reads and drops the data from the input file until a line feed is reached.
 */
void FileWrapper_nextString(FileWrapper *this_) {
    size_t ptr = this_->bufptr, end = this_->bufend;
    char *buf = this_->buffer;
    
    do {
        while (ptr < end) {
            if (buf[ptr++] == '\n') { // Line feed found. We need to increment the pointer to drop it before returning.
                this_->bufptr = ptr;
                this_->bufend = end;
                return;
            }
        }
        ptr = 0;
    } while ((end = fread(buf, sizeof(char), FILEWRAPPER_BUFFER_SIZE, this_->theFile)) > 0);
    // if we read a non-null number of characters from the stream the input file is not over.
    
    // We're not at the end of file here.
    this_->bufptr = 0;
    this_->bufend = 0;
}

/*!
 \brief Returns \c true if the buffer is empty and the file is over, \c false otherwise.
 */
bool FileWrapper_eof(FileWrapper *this_) {
    return this_->bufptr >= this_->bufend && feof(this_->theFile);
}

/*!
 \brief Creates a file wrapper that reads from the specified file.
 */
FileWrapper *makeFileWrapper(FILE *theFile) {
    FileWrapper *this_ = (FileWrapper *)malloc(sizeof(FileWrapper));
    this_->theFile = theFile;
    this_->buffer = (char *)malloc(sizeof(char) * FILEWRAPPER_BUFFER_SIZE);
    this_->bufptr = 0;
    this_->bufend = 0;
    
    return this_;
}

/*!
 \brief Frees the file wrapper.
 \note This <b>doesn't close the pointed file</b>.
 */
void destroyFileWrapper(FileWrapper *this_) {
    free(this_->buffer);
    free(this_);
}


struct __tm_state;
struct __transition;
struct __tm_mach;
struct __tm_tape;
struct __tm_controller;


/*!
 \brief ID of the state as specified by the input.
 */
typedef int state_id;

/*!
 \brief Possible moves of the control head.
 */
typedef enum {
    ControlHeadMoveLeft     = 0,     ///< The head has to move to the left.
    ControlHeadMoveStay     = 1,     ///< The head has to stay on the current cell.
    ControlHeadMoveRight    = 2,     ///< The head has to move to the right.
} ControlHeadMove;

/*!
 \brief Structure containing all the information about a transition between states.
 */
typedef struct __transition {
    char input;                         ///< Symbol to read on the tape in order to trigger the transition.
    char output;                        ///< Symbol to write to the current cell.
    ControlHeadMove move;               ///< Move that the control head needs to do.
    
    struct __tm_state *source;          ///< State before the transition.
    struct __tm_state *destination;     ///< State to reach after the transition.
    struct __transition *next;          ///< Next transition in the move list.
} Transition;

/*!
 \brief Chained list of transitions. Transitions contained in the same list share required input and state, so a list contains only non-deterministic moves to do from a specific state with a specific symbol.
 */
typedef struct {
    Transition *head;           ///< Pointer to the list head.
    int length;                 ///< Length of the list.
} MoveList;

#ifdef USE_HASH_AND_TREE

/*!
 \brief Colors of a red-black tree node.
 */
typedef enum {
    TreeNodeColorRed,
    TreeNodeColorBlack
} TreeNodeColor;

/*!
 \brief Entry of the edge hash table. (tree structure)
 */
typedef struct __edge_tree_entry {
    struct __edge_tree_entry *parent;   ///< Pointer to the parent node.
    
    char key;                           ///< Node key.
    TreeNodeColor color;                ///< Node color.
    
    MoveList *moves;                    ///< List of (non-deterministic) moves associated to the key.
    
    struct __edge_tree_entry *left;     ///< Pointer to the left child.
    struct __edge_tree_entry *right;    ///< Pointer to the right child.
} EdgeTreeNode;

/*!
 \brief Red black tree that divide moves of different input symbols sharing the same hash table slot.
 */
typedef struct {
    EdgeTreeNode *root;            ///< Tree root.Radice dell'albero.
    EdgeTreeNode *null;            ///< Node used to represent null leaves.
} EdgeTree;

/*!
 \brief Hash table used to optimise the access to edges that are adjacent to a node.
 */
typedef struct __edge_table {
    EdgeTree **slots;               ///< Hash table slots.
} EdgeTable;

#else

/*!
 \brief List block. Gives a faster access than the one given by red-black trees indexing symbols by their \c GROUP_BITS less significant bits.
 */
typedef struct {
    MoveList *moves[(1 << GROUP_BITS)]; ///< Array indexed by input symbols \c GROUP_BITS less significant bits.
} ListBlock;

#endif

/*!
 \brief Node representing the state of the Turing Machine control core.
 */
typedef struct __tm_state {
#ifdef USE_HASH_AND_TREE
    EdgeTable *moves;                                       ///< Hash table containing the possible moves that may be done starting from this state.
#else
    ListBlock *blocks[(MOVE_LIST_SLOTS >> GROUP_BITS)];     ///< Array indexed by input symbol (8 - \c GROUP_BITS) less significant bits, containing the moves that have to be done.
#endif
    
    bool accept;                                            ///< \c true if accepting state, \c false otherwise.
} State;

/*!
 \brief Slot entry for the state hash table. Also used as node for the chained list (hash tree with chaining).
 */
typedef struct __state_table_entry {
    state_id sid;                       ///< State ID
    State *state;                       ///< State object held by the entry
    struct __state_table_entry *next;   ///< Next entry in the list
} StateTableEntry;

/*!
 \brief Hash table with chaining holding the states. It is used to build the graph and to free all the nodes at the end.
 */
typedef struct {
    StateTableEntry **slots;            ///< Slot space with a length of \c STATE_TABLE_SLOTS
} StateTable;

/*!
 \brief Tape chunk containing a number of usable cells.
 */
typedef struct __tm_tape_chunk {
    char cells[CELLS_PER_CHUNK];            ///< Array containing the cells of the chunk.
    long refCount;                          ///< Number of controllers using this chunk.
    
    struct __tm_tape_chunk *prev;           ///< Pointer to the previous element. This field is handled by the \c ChunkSet class.
    struct __tm_tape_chunk *next;           ///< Pointer to the next element. This field is handled by the \c ChunkSet class.
} TapeChunk;

/*!
 \brief Structure representing a set of chunks.
 \note Although this is formally a chained list of chunks, it is <b>not</b> supposed to guarantee any order between contained chunks.
 */
typedef struct __tm_chunk_set {
    TapeChunk *head;                        ///< Pointer to the first element of the set.
    TapeChunk *tail;                        ///< Pointer to the last element of the set.
} ChunkSet;

/*!
 \brief Entity representing a control head of the Turing Machine. Different non-deterministic computations are represented by different instances of this structure.
 */
typedef struct __tm_controller {
    State *currentState;                    ///< Current state of the controller.
    struct __tm_tape *tape;                 ///< Pointer to the tape this head is on.
    int head;                               ///< Number indexing the element of the \c cells array in the chunk.
    
    TapeChunk *lastSourceChunk;             ///< The last source chunk requested by the controller.
    
    struct __tm_mach *machine;              ///< Pointer to the Turing Machine handling this controller.
    struct __tm_controller *next;           ///< Next controller. This field is handled by the \c TaskQueue class.
} Controller;

/*!
 \brief Structure representing the queue of controllers that need to go ahead with the computation. This is used for a breadth-first search on the computations tree.
 */
typedef struct {
    Controller *head;                       ///< Pointer to the first controller to extract.
    Controller *tail;                       ///< Pointer to the last controller inserted.
} TaskQueue;

/*!
 \brief Structure representing a tape node as it is held by the controller. This structure allows to handle the tape more efficiently without needing to always copy the chunks. Unlike chunks, these structures are not shared among controllers.
 */
typedef struct __tm_tape {
    TapeChunk *chunk;                       ///< Pointer to the chunk held by this tape.
#ifdef FAST_FORK
    long refCount;                          ///< Number of tapes this tape node joins - 1.
#endif
    
    struct __tm_tape *left;                 ///< Left node of the tape.
    struct __tm_tape *right;                ///< Right node of the tape.
} MachineTape;

/*!
 \brief Values indicating the outcome of a computation from the automaton.
 */
typedef enum {
    AutomatonOutcomeAccept    = 1,  ///< The Turing Machine accepted the input string.
    AutomatonOutcomeUndefined = 2,  ///< The Turing Machine couldn't determine anything because it reached the limit of steps in a computation branch.
    AutomatonOutcomeRefuse    = 3,  ///< The Turing Machine rejected the string in every computation branch.
} AutomatonOutcome;

/*!
 \brief Structure representing the source of a Turing Machine. The source provides controllers with source chunks, which are chunks containing the input string.
 \note A source is created for each string, and the source MUST leave the input file at the begin of the next string. Source chunks are one and only one for every matching part of the input string, and controllers will copy and replace the chunk in their tape if it needs to be modified.
 */
typedef struct {
    struct __tm_mach *machine;      ///< The Turing Machine using this source.
    ChunkSet *sourceChunks;         ///< Chunk set containing the source chunks extracted from the input file.
    
    FileWrapper *source;            ///< File wrapper that reads from the input file.
    bool inputIsOver;               ///< \c true if the input string is over, \c false if there is still something in the input string to read.
} MachineSource;

/*!
 \brief Structure representing a Turing Machine.
 */
typedef struct __tm_mach {
    StateTable *stateTable;          ///< State table.
    MachineSource *source;           ///< Source of the machine where input is extracted.
    
    long hardLimit;                  ///< Depth limit for the computations tree.
    
    ChunkSet *allocatedChunks;       ///< Chunk allocated by the TM.
    ChunkSet *recycledChunks;        ///< Chunk recyclable by the TM.
    
    TapeChunk *zeroChunk;            ///< A blank filled chunk held by the TM.
} TuringMachine;



/// TRANSITION

/*!
 \brief Allocates a new transition object and initializes it with the specified parameters.
 */
Transition *makeTransition(struct __tm_state *source, char input, char output, ControlHeadMove move, struct __tm_state *destination) {
    Transition *this_ = (Transition *)malloc(sizeof(Transition));
    this_->input = input;
    this_->source = source;
    
    this_->output = output;
    this_->move = move;
    this_->destination = destination;
    this_->next = NULL;
    return this_;
}

/*!
 \brief Destroys the transition and the next one, if any.
 */
void destroyTransition(Transition *this_) {
    if (this_) {
        destroyTransition(this_->next);
        free(this_);
    }
}


/// MOVE LIST

/*!
 \brief Pushes the given transition to the head of the list.
 */
void MoveList_push(MoveList *this_, Transition *transition) {
    transition->next = this_->head;
    this_->head = transition;
    this_->length += 1;
}

/*!
 \brief Builds an empty list of moves.
 */
MoveList *makeMoveList() {
    MoveList *this_ = (MoveList *)malloc(sizeof(MoveList));
    this_->head = NULL;
    this_->length = 0;
    
    return this_;
}


#ifdef USE_HASH_AND_TREE

/// EDGE TREE NODE

/*!
 \brief Creates a tree node setting the children pointers to the specified tree's null leaf.
 */
EdgeTreeNode *makeEdgeTreeNode(EdgeTree *tree, TreeNodeColor color) {
    EdgeTreeNode *this_ = (EdgeTreeNode *)malloc(sizeof(EdgeTreeNode));
    this_->moves = NULL;
    
    this_->color = color;
    this_->parent = NULL;
    this_->left = tree->null;
    this_->right = tree->null;
    
    return this_;
}


/// EDGE TREE (RED-BLACK TREE)

/*!
 \brief Rotates the node to the left.
 */
void EdgeTree_leftRotate(EdgeTree *this_, EdgeTreeNode *x) {
    EdgeTreeNode *y = x->right;
    x->right = y->left;
    
    if (y->left != this_->null) {
        y->left->parent = x;
    }
    y->parent = x->parent;
    
    if (x->parent == this_->null) {
        this_->root = y;
    } else if (x == x->parent->left) {
        x->parent->left = y;
    } else {
        x->parent->right = y;
    }
    
    y->left = x;
    x->parent = y;
}

/*!
 \brief Rotates the node to the right.
 */
void EdgeTree_rightRotate(EdgeTree *this_, EdgeTreeNode *x) {
    EdgeTreeNode *y = x->left;
    x->left = y->right;
    
    if (y->right != this_->null) {
        y->right->parent = x;
    }
    y->parent = x->parent;
    
    if (x->parent == this_->null) {
        this_->root = y;
    } else if (x == x->parent->right) {
        x->parent->right = y;
    } else {
        x->parent->left = y;
    }
    
    y->right = x;
    x->parent = y;
}

/*!
 \brief Fixes the red-black tree up.
 */
void EdgeTree_fixup(EdgeTree *this_, EdgeTreeNode *node) {
    if (node == this_->root) {
        this_->root->color = TreeNodeColorBlack;
    } else {
        EdgeTreeNode *x, *y;
        x = node->parent;
        
        if (x->color == TreeNodeColorRed) {
            if (x == x->parent->left) {
                y = x->parent->right;
                if (y->color == TreeNodeColorRed) {
                    x->color = TreeNodeColorBlack;
                    y->color = TreeNodeColorBlack;
                    x->parent->color = TreeNodeColorRed;
                    EdgeTree_fixup(this_, x->parent);
                } else {
                    if (node == x->right) {
                        node = x;
                        EdgeTree_leftRotate(this_, node);
                        x = node->parent;
                    }
                    x->color = TreeNodeColorBlack;
                    x->parent->color = TreeNodeColorRed;
                    EdgeTree_rightRotate(this_, x->parent);
                }
            } else {
                y = x->parent->left;
                if (y->color == TreeNodeColorRed) {
                    x->color = TreeNodeColorBlack;
                    y->color = TreeNodeColorBlack;
                    x->parent->color = TreeNodeColorRed;
                    EdgeTree_fixup(this_, x->parent);
                } else {
                    if (node == x->left) {
                        node = x;
                        EdgeTree_rightRotate(this_, node);
                        x = node->parent;
                    }
                    x->color = TreeNodeColorBlack;
                    x->parent->color = TreeNodeColorRed;
                    EdgeTree_leftRotate(this_, x->parent);
                }
            }
        }
    }
}

/*!
 \brief Returns the node for the associated symbol. The node is created if it doesn't exist.
 */
EdgeTreeNode *EdgeTree_getOrCreateNode(EdgeTree *this_, char fromSymbol) {
    EdgeTreeNode *node = this_->root;
    EdgeTreeNode *parent = this_->null;
    
    while (node != this_->null) {
        parent = node;
        if (fromSymbol < node->key) {
            node = node->left;
        } else if (fromSymbol > node->key) {
            node = node->right;
        } else return node;
    }
    
    EdgeTreeNode *newNode = makeEdgeTreeNode(this_, TreeNodeColorRed);
    newNode->key = fromSymbol;
    
    newNode->parent = parent;
    if (parent == this_->null) {
        this_->root = newNode;
    } else {
        if (newNode->key < parent->key) {
            parent->left = newNode;
        } else {
            parent->right = newNode;
        }
    }
    
    EdgeTree_fixup(this_, newNode); // Let's fixup the tree.
    return newNode;
}

/*!
 \brief Builds an empty edge tree.
 */
EdgeTree *makeEdgeTree() {
    EdgeTree *this_ = (EdgeTree *)malloc(sizeof(EdgeTree));
    this_->null = makeEdgeTreeNode(this_, TreeNodeColorBlack); // null leaf children will be set to NULL
    this_->root = this_->null;
    
    this_->null->left = this_->null;
    this_->null->right = this_->null;
    
    return this_;
}

/*!
 \brief Deletes the tree node, recursively destroying all the children.
 \note Null leaves won't be touched.
 */
void destroyEdgeTreeNode(EdgeTree *this_, EdgeTreeNode *node) {
    if (node != this_->null) {
        destroyEdgeTreeNode(this_, node->left);
        destroyEdgeTreeNode(this_, node->right);
        
        destroyTransition(node->moves->head);
        
        free(node->moves);
        free(node);
    }
}


/// EDGE TABLE

/*!
 \brief Hash function for the edge table.
 \note Only bitwise operations are used to improve the computation time.
 */
#define EdgeTable_hash(symbol) ((((symbol) << 2) ^ (symbol)) & (EDGE_TABLE_SLOTS - 1))

/*!
 \brief Add the transition to the hash table. If the tree in the matching slot doesn't exist then it is created.
 */
void EdgeTable_createEntry(EdgeTable *this_, char fromSymbol, Transition *transition) {
    int hash = EdgeTable_hash(fromSymbol);
    EdgeTree *tree = this_->slots[hash];
    
    if (!tree) { // if it doesn't exist then we create it.
        tree = makeEdgeTree();
        this_->slots[hash] = tree;
    }
    
    EdgeTreeNode *entryNode = EdgeTree_getOrCreateNode(tree, fromSymbol);
    
    if (!entryNode->moves) {
        entryNode->moves = makeMoveList();
    }
    
    MoveList_push(entryNode->moves, transition);
}

const MoveList *EdgeTable_lookup(const EdgeTable *this_, char symbol) {
    if (this_) {
        const EdgeTree *const tree = this_->slots[EdgeTable_hash(symbol)];
        
        if (tree) {
            const EdgeTreeNode *node = tree->root;
            const EdgeTreeNode *const nullNode = tree->null;
            
            while (node != nullNode) {
                if (symbol < node->key) {
                    node = node->left;
                } else if (symbol > node->key) {
                    node = node->right;
                } else {
                    return node->moves;
                }
            }
        }
    }
    return NULL;
}

/*!
 \brief Builds an empty edge table.
 */
EdgeTable *makeEdgeTable() {
    EdgeTable *this_ = (EdgeTable *)malloc(sizeof(EdgeTable));
    this_->slots = (EdgeTree **)calloc(EDGE_TABLE_SLOTS, sizeof(EdgeTree *));
    
    return this_;
}

/*!
 \brief Destroys the edge table freeing all the memory occupied by it.
 */
void destroyEdgeTable(EdgeTable *this_) {
    for (int i = 0; i < EDGE_TABLE_SLOTS; i++) {
        EdgeTree *tree = this_->slots[i];
        if (tree) {
            destroyEdgeTreeNode(tree, tree->root);
            
            free(tree->null);
            free(tree);
        }
    }
    
    free(this_->slots);
    free(this_);
}

#else

/*!
 \brief Returns an empty list block.
 */
ListBlock *makeListBlock() {
    ListBlock *this_ = (ListBlock *)malloc(sizeof(ListBlock));
    memset(this_->moves, 0, (1 << GROUP_BITS) * sizeof(MoveList *));
    
    return this_;
}

#endif


/// STATE (GRAPH NODE)

/*!
 \brief Returns a list of non-deterministic moves to do with the specified configuration, or \c NULL if there are no associated moves.
 */
#ifdef USE_HASH_AND_TREE
#define State_getMoveList(this_, symbol) (EdgeTable_lookup((this_)->moves, (symbol)))
#else
MoveList *State_getMoveList(State *this_, char symbol) {
    ListBlock *block = this_->blocks[(unsigned char)(symbol) >> GROUP_BITS];
    return block ? block->moves[(unsigned char)(symbol) & ((1 << GROUP_BITS) - 1)] : NULL;
}
#endif

/*!
 \brief Adds an edge going out from the state, with the specified parameters.
 */
void State_addEdge(State *this_, char fromSymbol, char toSymbol, ControlHeadMove move, State *destination) {
#ifdef USE_HASH_AND_TREE
    if (!this_->moves) {
        this_->moves = makeEdgeTable();
    }
    
    EdgeTable_createEntry(this_->moves, fromSymbol, makeTransition(this_, fromSymbol, toSymbol, move, destination));
#else
    ListBlock *block = this_->blocks[(unsigned char)(fromSymbol) >> GROUP_BITS];
    if (!block) {
        block = this_->blocks[(unsigned char)(fromSymbol) >> GROUP_BITS] = makeListBlock();
    }
    MoveList *list = block->moves[(unsigned char)(fromSymbol) & ((1 << GROUP_BITS) - 1)];
    if (!list) {
        list = block->moves[(unsigned char)(fromSymbol) & ((1 << GROUP_BITS) - 1)] = makeMoveList();
    }
    MoveList_push(list, makeTransition(this_, fromSymbol, toSymbol, move, destination));
#endif
}

/*!
 \brief Builds an empty state.
 */
State *makeState() {
    State *this_ = (State *)malloc(sizeof(State));
#ifdef USE_HASH_AND_TREE
    this_->moves = NULL;
#else
    memset(this_->blocks, 0, (MOVE_LIST_SLOTS >> GROUP_BITS) * sizeof(MoveList *));
#endif
    this_->accept = false;
    
    return this_;
}


/// STATE TABLE SLOT LIST

/*!
 \brief Allocated a new entry for the state table with the given parameters.
 */
StateTableEntry *pushStateTableEntry(StateTableEntry *next, state_id sid, State *state) {
    StateTableEntry *this_ = (StateTableEntry *)malloc(sizeof(StateTableEntry));
    this_->next = next;
    this_->sid = sid;
    this_->state = state;
    
    return this_;
}

/*!
 \brief Visits the list and looks for an entry with the specified state id.
 \return The state with the matching id, or \c NULL if the entry does not exist.
 */
State *StateTableEntry_getStateById(StateTableEntry *entry, state_id sid) {
    while (entry) {
        if (entry->sid == sid) {
            return entry->state;
        }
        
        entry = entry->next;
    }
    
    return NULL;
}


/// STATE TABLE

/*!
 \brief Hash function used by the state hash table.
 \note Assuming that state id are contiguous and starting from 0, the division method is suitable. Moreover, a power of 2 is needed for the slot space dimension in order to use bitwise operations.
 */
#define StateTable_hash(state) ((state) & (STATE_TABLE_SLOTS - 1))

/*!
 \brief Returns the state in the table with the specified ID.
 */
#define StateTable_getStateById(this_, sid) (StateTableEntry_getStateById((this_)->slots[StateTable_hash(sid)], (sid)))

/*!
 \brief Returns the state in the hash table with the specified state id. If it does not exist then it is created.
 */
State *StateTable_getOrCreateEntry(StateTable *this_, state_id sid) {
    int slot = StateTable_hash(sid);
    
    State *state = StateTableEntry_getStateById(this_->slots[slot], sid);
    if (!state) {
        state = makeState();
        
        // Let's insert a new entry to the head containing the newly created state.
        this_->slots[slot] = pushStateTableEntry(this_->slots[slot], sid, state);
    }
    
    return state;
}

/*!
 \brief Builds a state table reading from the specified input file.
 \note Remember to deallocate the memory <b>using destroyStateTable()</b>
 */
StateTable *makeStateTable(FILE *input) {
    StateTable *this_ = (StateTable *)malloc(sizeof(StateTable));
    this_->slots = (StateTableEntry **)calloc(STATE_TABLE_SLOTS, sizeof(StateTableEntry *));
    
    char buffer[30];
    fgets(buffer, 30, input);
    assert(strbeg(buffer, "tr") && "'tr' mancante!");
    
    fgets(buffer, 30, input);
    while (!strbeg(buffer, "acc")) { // TRANSITION READING
        // We'll go ahead until we find the beginning of the accepting states list.
        
        state_id fromState, toState;
        char fromSymbol, toSymbol, move;
        
        sscanf(buffer, "%d %c %c %c %d\n", &fromState, &fromSymbol, &toSymbol, &move, &toState);
        
        State *s1 = StateTable_getOrCreateEntry(this_, fromState);
        State *s2 = StateTable_getOrCreateEntry(this_, toState);
        
        State_addEdge(s1, fromSymbol, toSymbol, moveToInt(move), s2);
        
        fgets(buffer, 30, input);
    }
    
    fgets(buffer, 30, input);
    while (!strbeg(buffer, "max")) { // ACCEPTING STATES READING
        state_id sid;
        sscanf(buffer, "%d", &sid);
        
        State *state = StateTable_getStateById(this_, sid);
        if (state) {
            state->accept = true;
        }
        
        fgets(buffer, 30, input);
    }
    
    return this_;
}

/*!
 \brief Destroys the state table freeing all the memory occupied by it.
 \warning Beware of dangling pointers! Use this function only before exiting.
 */
void destroyStateTable(StateTable *this_) {
    for (int i = 0; i < STATE_TABLE_SLOTS; i++) {
        StateTableEntry *entry = this_->slots[i];
        while (entry) {
            State *state = entry->state;
            
#ifdef USE_HASH_AND_TREE
            if (state->moves) {
                destroyEdgeTable(state->moves);
            }
#else
            for (int i = 0; i < (MOVE_LIST_SLOTS >> GROUP_BITS); i++) {
                ListBlock *const listBlock = state->blocks[i];
                if (listBlock) {
                    for (int j = 0; j < (1 << GROUP_BITS); j++) {
                        MoveList *list = listBlock->moves[j];
                        if (list) {
                            destroyTransition(list->head);
                            free(list);
                        }
                    }
                    free(listBlock);
                }
            }
#endif
            
            StateTableEntry *toFree = entry;
            entry = entry->next;
            
            free(state);
            free(toFree);
        }
    }
    free(this_->slots);
    free(this_);
}


/// CHUNK SET (DOUBLE CHAINED CHUNK LIST)

/*!
 \brief Adds the specified chunk to the set (after the tail).
 */
void ChunkSet_add(ChunkSet *this_, TapeChunk *elem) {
    if (!this_->head) {
        this_->head = elem;
        elem->prev = NULL;
    } else {
        this_->tail->next = elem;
        elem->prev = this_->tail;
    }
    this_->tail = elem;
    elem->next = NULL;
}

/*!
 \brief Adds all the chunks of the specified set to the set (after the tail).
 \note Il set passato viene svuotato.
 */
void ChunkSet_addAll(ChunkSet *this_, ChunkSet *set) {
    if (this_->tail) {
        this_->tail->next = set->head;
    }
    if (set->head) {
        set->head->prev = this_->tail;
        this_->tail = set->tail;
        if (!this_->head) {
            this_->head = set->head;
        }
    }
    
    set->head = NULL;
    set->tail = NULL;
}

/*!
 \brief Removes the specified chunk from the set.
 */
void ChunkSet_remove(ChunkSet *this_, TapeChunk *elem) {
    if (elem->next) {
        elem->next->prev = elem->prev;
    } else {
        this_->tail = elem->prev;
    }
    
    if (elem->prev) {
        elem->prev->next = elem->next;
    } else {
        this_->head = elem->next;
    }
}

/*!
 \brief Extracts a chunk from (the head of) the set.
 */
TapeChunk *ChunkSet_extract(ChunkSet *this_) {
    if (this_->head) {
        TapeChunk *ret = this_->head;
        this_->head = ret->next;
        if (this_->head) {
            this_->head->prev = NULL;
        } else {
            this_->tail = NULL;
        }
        return ret;
    }
    return NULL;
}

/*!
 \brief Empties the set, freeing all the contained chunks.
 */
void ChunkSet_empty(ChunkSet *this_) {
    TapeChunk *node = this_->head;
    while (node) {
        TapeChunk *next = node->next;
        free(node);
        node = next;
    }
    
    this_->head = NULL;
    this_->tail = NULL;
}

/*!
 \brief Builds an empty chunk set.
 */
ChunkSet *makeChunkSet() {
    ChunkSet *this_ = (ChunkSet *)malloc(sizeof(ChunkSet));
    this_->head = NULL;
    this_->tail = NULL;
    
    return this_;
}

/*!
 \brief Empties and frees the set.
 */
void destroyChunkSet(ChunkSet *this_) {
    ChunkSet_empty(this_);
    
    free(this_);
}


/// TASK QUEUE

/*!
 \brief Inserts the given controller to the tail of the queue.
 */
void TaskQueue_enqueue(TaskQueue *this_, Controller *controller) {
    if (!this_->head) {
        this_->head = controller;
    } else {
        this_->tail->next = controller;
    }
    this_->tail = controller;
    controller->next = NULL;
}

/*!
 \brief Extracts and returns the first controller of the queue.
 */
Controller *TaskQueue_dequeue(TaskQueue *this_) {
    Controller *dequeued = this_->head;
    this_->head = dequeued->next;
    if (!this_->head) {
        this_->tail = NULL;
    }
    
    return dequeued;
}

/*!
 \brief Creates an empty task queue.
 */
TaskQueue *makeTaskQueue() {
    TaskQueue *this_ = (TaskQueue *)malloc(sizeof(TaskQueue));
    this_->head = NULL;
    this_->tail = NULL;
    return this_;
}

/*!
 \brief Frees the queue.
 \note No controllers are freed by this functions. The queue needs to be emptied first.
 */
void destroyTaskQueue(TaskQueue *this_) {
    free(this_);
}


/// TAPE CHUNK

/*!
 \brief Creates a chunk containing all blank values.
 */
TapeChunk *makeBlankChunk() {
    TapeChunk *this_ = (TapeChunk *)malloc(sizeof(TapeChunk));
    this_->refCount = 1;
    
    memset(this_->cells, SYMBOL_BLANK, CELLS_PER_CHUNK * sizeof(char));
    return this_;
}

/*!
 \brief Decrements the chunk reference counter. If this counter reaches 0 the chunk is freed.
 \note If \c RECYCLE_NOREF_CHUNKS is defined, the chunk is added to the recycledChunks set.
 */
void releaseChunk(TapeChunk *this_, TuringMachine *tm) {
    this_->refCount -= 1;
    if (this_->refCount <= 0) {
        ChunkSet_remove(tm->allocatedChunks, this_);
        
#ifdef RECYCLE_NOREF_CHUNKS
        ChunkSet_add(tm->recycledChunks, this_);
#else
        free(this_);
#endif
    }
}

/*!
 \brief Creates a copy of the specified chunk, using the specified Turing Machine as allocator.
 \note Il chunk passato viene rilasciato da questa funzione.
 */
TapeChunk *copyChunk(TuringMachine *tm, TapeChunk *chunk) {
    TapeChunk *this_;
    
#ifdef RECYCLE_CHUNKS
    if (tm->recycledChunks->head) {
        this_ = ChunkSet_extract(tm->recycledChunks);
    } else
#endif
    {
        this_ = (TapeChunk *)malloc(sizeof(TapeChunk));
    }
    
    ChunkSet_add(tm->allocatedChunks, this_);
    this_->refCount = 1;
    memcpy(this_->cells, chunk->cells, CELLS_PER_CHUNK * sizeof(char));

    releaseChunk(chunk, tm);
    return this_;
}


/// TAPE NODE

/*!
 \brief Increments by the specified quantity the chunk pointed by this node of the tape.
 */
#define MachineTape_retainChunk(this_, count) ((this_)->chunk->refCount += (count))

/*!
 \brief Builds an empty tape node.
 */
MachineTape *makeMachineTape() {
    MachineTape *this_ = (MachineTape *)malloc(sizeof(MachineTape));
#ifdef FAST_FORK
    this_->refCount = 0;
#endif
    this_->chunk = NULL;
    
    this_->left = NULL;
    this_->right = NULL;
    return this_;
}

/*!
 \brief Copies the specified tape node.
 \note This does not increment the reference count of the chunk pointed by the node.
 */
MachineTape *cloneMachineTape(MachineTape *tape) {
    MachineTape *this_ = (MachineTape *)malloc(sizeof(MachineTape));
    this_->chunk = tape->chunk;
    
#ifdef FAST_FORK
    this_->refCount = 0;
    this_->left = tape->left;
    this_->right = tape->right;
#else
    this_->left = NULL;
    this_->right = NULL;
#endif
    return this_;
}

/*!
 \brief Frees the tape node.
 \param relChunk if \c true chunks will be released.
 */
void destroyMachineTape(MachineTape *this_, bool relChunk, TuringMachine *tm) {
    if (relChunk) {
        releaseChunk(this_->chunk, tm);
    }
    free(this_);
}


/// MACHINE SOURCE

/*!
 \brief Tries to read from the input file taking the first \c CELLS_PER_CHUNK characters.
 \return A newly created source chunk containing the new characters from the input, with leading blanks if the source runs out of characters.
 */
TapeChunk *MachineSource_getNewChunk(MachineSource *this_) {
    if (this_->inputIsOver) {
        return NULL;
    }
    
    TapeChunk *newChunk;
#ifdef RECYCLE_CHUNKS
    TuringMachine *const tm = this_->machine;
    if (tm->recycledChunks->head) {
        newChunk = ChunkSet_extract(tm->recycledChunks);
    } else
#endif
    {
        newChunk = (TapeChunk *)malloc(sizeof(TapeChunk));
    }
    newChunk->refCount = 1;
    // We need an additional reference from the list of the machine source for this type of chunks, in order for controllers to copy it on write.
    
    char *cells = newChunk->cells;
    int i = 0;
    while (i < CELLS_PER_CHUNK) {
        char c = FileWrapper_getChar(this_->source);
        if (c == '\n') {
            this_->inputIsOver = true;
            break;
        }
        
        cells[i++] = c;
    }
    
    while (i < CELLS_PER_CHUNK) {
        cells[i++] = SYMBOL_BLANK;
    }
    
    return newChunk;
}

/*!
 \brief Returns the next source chunk that needs to be read by the controller. If the source chunks is not in memory, a read from the input will be attempted.
 */
TapeChunk *MachineSource_getNextSourceChunk(MachineSource *this_, Controller *C) {
    TapeChunk *lastSourceChunk = C->lastSourceChunk;
    if (lastSourceChunk) {
        if (!lastSourceChunk->next) {
            TapeChunk *const newChunk = MachineSource_getNewChunk(this_);
            if (newChunk) {
                ChunkSet_add(this_->sourceChunks, newChunk);
            }
        }
        
        lastSourceChunk = C->lastSourceChunk = lastSourceChunk->next;
        if (lastSourceChunk) {
            lastSourceChunk->refCount += 1;
            return lastSourceChunk;
        }
    }
    return NULL;
}

/*!
 \brief If input is not over, eats the remaining part of the input string such that the file wrapper will be ready to read the next one.
 */
void MachineSource_eatString(MachineSource *this_) {
    if (!this_->inputIsOver) {
        FileWrapper_nextString(this_->source);
        this_->inputIsOver = false;
    }
}

/*!
 \brief Creates a source for the specified machine, taking input strings from the given file wrapper.
 */
MachineSource *makeMachineSource(TuringMachine *tm, FileWrapper *source) {
    MachineSource *this_ = (MachineSource *)malloc(sizeof(MachineSource));
    this_->machine = tm;
    this_->source = source;
    this_->inputIsOver = false;
    
    this_->sourceChunks = makeChunkSet();
    ChunkSet_add(this_->sourceChunks, MachineSource_getNewChunk(this_));
    
    return this_;
}

/*!
 \brief Frees the source and not recycled source chunks, if any.
 */
void destroyMachineSource(MachineSource *this_) {
    destroyChunkSet(this_->sourceChunks);
    free(this_);
}


/// CONTROLLER

/*!
 \brief Returns the symbol in the cell that is under the head of the given controller.
 */
#define Controller_readCell(this_) ((this_)->tape->chunk->cells[(this_)->head])

/*!
 \brief Writes the specified symbol on the cell under the head of the controller. If the chunk is shared with other controllers, then a copy on write will be done.
 */
void Controller_writeCell(Controller *this_, char symbol) {
    MachineTape *tape = this_->tape;
    TapeChunk *chunk = tape->chunk;
    
    if (chunk->refCount > 1) {
        chunk = tape->chunk = copyChunk(this_->machine, chunk);
    }
    chunk->cells[this_->head] = symbol;
}

/*!
 \brief Moves the head of the controller to the left by a cell. In case it goes out of the bounds of the chunk, the needed operations to change it will be done.
 */
void Controller_moveToLeft(Controller *this_) {
    this_->head -= 1;
    if (this_->head < 0) {
        this_->head = CELLS_PER_CHUNK - 1;
        
        MachineTape *const currentTape = this_->tape;
        MachineTape *targetTape = currentTape->left;
        if (!targetTape) {
            targetTape = makeMachineTape();
        }
#ifdef FAST_FORK
        else if (targetTape->refCount > 0) {
            targetTape->refCount -= 1;
            MachineTape_retainChunk(targetTape, 1);
            targetTape = cloneMachineTape(targetTape);
            
            if (targetTape->left) {
                targetTape->left->refCount += 1;
            }
        }
#endif
        currentTape->left = targetTape;
        targetTape->right = currentTape;
        this_->tape = targetTape;
        
        MachineTape *const tape = this_->tape;
        if (!tape->chunk) {
            tape->chunk = this_->machine->zeroChunk;
            tape->chunk->refCount += 1;
        }
    }
}

/*!
 \brief Moves the head of the controller to the right by a cell. In case it goes out of the bounds of the chunk, the needed operations to change it will be done.
 */
void Controller_moveToRight(Controller *this_) {
    this_->head += 1;
    if (this_->head >= CELLS_PER_CHUNK) {
        this_->head = 0;
        
        MachineTape *const currentTape = this_->tape;
        MachineTape *targetTape = currentTape->right;
        if (!targetTape) {
            targetTape = makeMachineTape();
        }
#ifdef FAST_FORK
        else if (targetTape->refCount > 0) {
            targetTape->refCount -= 1;
            MachineTape_retainChunk(targetTape, 1);
            targetTape = cloneMachineTape(targetTape);
            
            if (targetTape->right) {
                targetTape->right->refCount += 1;
            }
        }
#endif
        currentTape->right = targetTape;
        targetTape->left = currentTape;
        this_->tape = targetTape;
        
        MachineTape *const tape = this_->tape;
        if (!tape->chunk) {
            TuringMachine *const tm = this_->machine;
            TapeChunk *newChunk = MachineSource_getNextSourceChunk(tm->source, this_);
            if (newChunk) {
                tape->chunk = newChunk;
            } else {
                tape->chunk = tm->zeroChunk;
                tape->chunk->refCount += 1;
            }
        }
    }
}

/*!
 \brief Executes the specified transition with the controller configuration.
 \param content The symbol under the controller head.
 */
bool Controller_executeTransition(Controller *this_, char content, const Transition *T) {
    if (content != T->output) {
        Controller_writeCell(this_, T->output);
    }
    
    switch (T->move) {
        case ControlHeadMoveLeft:
            Controller_moveToLeft(this_);
            break;
        case ControlHeadMoveRight:
            Controller_moveToRight(this_);
            break;
        default: break;
    }
    
    this_->currentState = T->destination;
    return T->destination->accept;
}

/*!
 \brief Builds the first controller for the computation.
 */
Controller *makeFirstController(TuringMachine *tm) {
    Controller *this_ = (Controller *)malloc(sizeof(Controller));
    this_->machine = tm;
    
    this_->currentState = StateTable_getStateById(tm->stateTable, 0); // Initial state of the machine.
    
    this_->tape = makeMachineTape();
    this_->head = 0;
    
    this_->lastSourceChunk = tm->source->sourceChunks->head;
    this_->tape->chunk = this_->lastSourceChunk;
    this_->lastSourceChunk->refCount += 1;
    // First source chunk. This is allocated immediately after the source allocation.
    
    this_->next = NULL;
    return this_;
}

/*!
 \brief Clones the controller, getting the tape ready for a non-determinism.
 */
Controller *cloneController(Controller *C) {
    Controller *this_ = (Controller *)malloc(sizeof(Controller));
    this_->currentState = C->currentState;
    this_->lastSourceChunk = C->lastSourceChunk;
    this_->machine = C->machine;
    
    this_->head = C->head;
    
    this_->next = NULL;
    this_->tape = cloneMachineTape(C->tape);
    
#ifndef FAST_FORK
    MachineTape *node = this_->tape;
    MachineTape *toCopy = C->tape->right;
    while (toCopy) {
        node->right = cloneMachineTape(toCopy);
        node->right->left = node;
        
        node = node->right;
        toCopy = toCopy->right;
    }
    
    node = this_->tape;
    toCopy = C->tape->left;
    while (toCopy) {
        node->left = cloneMachineTape(toCopy);
        node->left->right = node;
        
        node = node->left;
        toCopy = toCopy->left;
    }
#endif
    
    return this_;
}

/*!
 \brief Increments the reference counter of all the chunks used by the controller.
 */
void Controller_retainChunks(Controller *this_, int count) {
#ifdef FAST_FORK
    MachineTape *const tape = this_->tape;
    MachineTape_retainChunk(tape, count);
    
    if (tape->left) {
        tape->left->refCount += count;
    }
    if (tape->right) {
        tape->right->refCount += count;
    }
#else
    MachineTape *tape = this_->tape->right;
    while (tape) {
        MachineTape_retainChunk(tape, count);
        tape = tape->right;
    }
    
    tape = this_->tape;
    while (tape) {
        MachineTape_retainChunk(tape, count);
        tape = tape->left;
    }
#endif
}

/*!
 \brief Frees the controller, and every node of the tape used by it.
 \param relChunks if \c true , also chunks will be released.
 */
void destroyController(Controller *this_, bool relChunks) {
    TuringMachine *const tm = this_->machine;
    MachineTape *tape = this_->tape->right;
    while (tape) {
#ifdef FAST_FORK
        if (tape->refCount > 0) {
            tape->refCount -= 1;
            break;
        }
#endif
        MachineTape *next = tape->right;
        destroyMachineTape(tape, relChunks, tm);
        tape = next;
    }
    
    tape = this_->tape;
    while (tape) {
#ifdef FAST_FORK
        if (tape->refCount > 0) {
            tape->refCount -= 1;
            break;
        }
#endif
        MachineTape *next = tape->left;
        destroyMachineTape(tape, relChunks, tm);
        tape = next;
    }
    free(this_);
}


/// TURING MACHINE

/*!
 \brief Simulates a computation of the Turing Machine, with the input string made up of all the characters of the source, until the line feed.
 */
AutomatonOutcome TuringMachine_doCompute(TuringMachine *this_) {
    AutomatonOutcome outcome = AutomatonOutcomeUndefined;
    
    TaskQueue *queue, *newQueue;
    queue = makeTaskQueue();
    newQueue = makeTaskQueue();
    
    TaskQueue_enqueue(queue, makeFirstController(this_));
    
    long stepNumber = 0;
    while (stepNumber < this_->hardLimit) {
        
        while (queue->head) {
            Controller *controller = TaskQueue_dequeue(queue);
            
            char content = Controller_readCell(controller);
            const MoveList *moves = State_getMoveList(controller->currentState, content);
            if (moves) {
                const Transition *T = moves->head;
                if (moves->length > 1) {
                    Controller_retainChunks(controller, moves->length - 1);
                }
                
                while (T->next) {
                    Controller *forkC = cloneController(controller);
                    
                    TaskQueue_enqueue(newQueue, forkC);
                    if (Controller_executeTransition(forkC, content, T)) {
                        outcome = AutomatonOutcomeAccept;
                        goto halt_tm;
                    }
                    
                    T = T->next;
                }
                
                TaskQueue_enqueue(newQueue, controller);
                if (Controller_executeTransition(controller, content, T)) {
                    outcome = AutomatonOutcomeAccept;
                    goto halt_tm;
                }
            } else {
                destroyController(controller, true);
            }
        }
        
        TaskQueue *temp = queue;
        queue = newQueue;
        newQueue = temp;
        
        if (!queue->head) {
            outcome = AutomatonOutcomeRefuse;
            goto halt_tm;
        }
        
        stepNumber += 1;
    }
    
    
halt_tm:
    while (queue->head) {
        destroyController(TaskQueue_dequeue(queue), false);
    }
    while (newQueue->head) {
        destroyController(TaskQueue_dequeue(newQueue), false);
    }
    
#ifdef RECYCLE_END_CHUNKS
    // PUT ALL THE CHUNKS IN THE RECYCLE SET
    ChunkSet_addAll(this_->recycledChunks, this_->allocatedChunks);
#else
    ChunkSet_empty(this_->allocatedChunks);
#endif
    
    destroyTaskQueue(queue);
    destroyTaskQueue(newQueue);
    return outcome;
}

/*!
 \brief Starts the computation of the Turing Machine with the input given by the string contained in the specified file.
 \note The string <b>is completely read</b> by this method. Make sure you are at the begin of the line.
 */
AutomatonOutcome TuringMachine_startComputation(TuringMachine *this_, FileWrapper *input) {
    this_->source = makeMachineSource(this_, input);
    
    AutomatonOutcome outcome = TuringMachine_doCompute(this_);
    
    // If the input is not all read by the source, read and drop it until you find the line feed.
    MachineSource_eatString(this_->source);
    
#ifdef RECYCLE_SOURCE_CHUNKS
    // Let's recycle the source chunks, too.
    ChunkSet_addAll(this_->recycledChunks, this_->source->sourceChunks);
#endif
    
    destroyMachineSource(this_->source);
    return outcome;
}

/*!
 \brief Builds a Turing Machine from the given input file.
 */
TuringMachine *makeTuringMachine(FILE *input) {
    TuringMachine *this_ = (TuringMachine *)malloc(sizeof(TuringMachine));
    this_->allocatedChunks = makeChunkSet();
    this_->recycledChunks = makeChunkSet();
    this_->zeroChunk = makeBlankChunk();
    
    this_->stateTable = makeStateTable(input);
    fscanf(input, "%ld\n", &this_->hardLimit); // makeStateTable ha già fatto il parsing fino a max compreso.
    
    return this_;
}

/*!
 \brief Destroys the Turing Machine, freeing all the memory occupied by it.
 */
void destroyTuringMachine(TuringMachine *this_) {
    destroyStateTable(this_->stateTable);
    
    destroyChunkSet(this_->allocatedChunks);
    destroyChunkSet(this_->recycledChunks);
    free(this_->zeroChunk);
    
    free(this_);
}

int main(int argc, const char *argv[]) {
    
    TuringMachine *tm = makeTuringMachine(stdin);
    FileWrapper *fw = makeFileWrapper(stdin);
    
    char buffer[20];
    fgets(buffer, 20, stdin);
    
    while (!FileWrapper_eof(fw)) {
        switch (TuringMachine_startComputation(tm, fw)) {
            case AutomatonOutcomeAccept:
                printf("1\n");
                break;
            case AutomatonOutcomeRefuse:
                printf("0\n");
                break;
            case AutomatonOutcomeUndefined:
                printf("U\n");
                break;
        }
    }
    
    destroyTuringMachine(tm);
    destroyFileWrapper(fw);
    
    return 0;
}
