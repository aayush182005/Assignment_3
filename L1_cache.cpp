
#include <iostream>
#include <fstream>
#include <vector>
#include <string>
#include <sstream>
#include <cstdint>
#include <cmath>
#include <queue>
#include <algorithm>
#include <unordered_map>
#include <iomanip>
#include <getopt.h>

// MESI Protocol States
enum class MESIState {
    INVALID,    // I
    SHARED,     // S
    EXCLUSIVE,  // E
    MODIFIED    // M
};

// Bus Transaction Types
enum class BusTransaction {
    BUSRD,      // Bus Read
    BUSRDX,     // Bus Read Exclusive
    FLUSH,      // Write back to memory
    INVALIDATE  // Invalidate command
};

// Bus Request Structure
struct BusRequest {
    int coreId;                 // Which core initiated the request
    BusTransaction type;        // Type of bus transaction
    uint32_t address;           // Memory address
    bool handled;               // Whether this request has been handled
    int initiatedCycle;         // The cycle when this request was initiated
    
    BusRequest(int id, BusTransaction t, uint32_t addr, int cycle) 
        : coreId(id), type(t), address(addr), handled(false), initiatedCycle(cycle) {}
};

// Cache Line Structure
struct CacheLine {
    uint32_t tag;
    MESIState state;
    bool valid;
    bool dirty;
    uint32_t lru;               // For LRU replacement
    std::vector<uint8_t> data;  // Data block
    
    CacheLine(int blockSize) 
        : tag(0), state(MESIState::INVALID), valid(false), dirty(false), lru(0) {
        data.resize(blockSize, 0);
    }
};

// Cache Set Structure
struct CacheSet {
    std::vector<CacheLine> lines;
    
    CacheSet(int associativity, int blockSize) {
        for (int i = 0; i < associativity; i++) {
            lines.push_back(CacheLine(blockSize));
        }
    }
};

// Statistics for each core
struct CoreStats {
    int readCount;
    int writeCount;
    int totalCycles;
    int idleCycles;
    int misses;
    int accesses;
    int evictions;
    int writebacks;
    
    CoreStats() : readCount(0), writeCount(0), totalCycles(0), idleCycles(0), 
                  misses(0), accesses(0), evictions(0), writebacks(0) {}
};

// Global statistics
struct GlobalStats {
    int invalidations;
    int dataTraffic;
    
    GlobalStats() : invalidations(0), dataTraffic(0) {}
};

// Cache Class
class Cache {
private:
    int coreId;
    int setIndexBits;
    int associativity;
    int blockBits;
    int sets;
    int blockSize;
    int wordSize;
    
    std::vector<CacheSet> cacheSets;
    
public:
    Cache(int id, int s, int E, int b) 
        : coreId(id), setIndexBits(s), associativity(E), blockBits(b) {
        sets = 1 << setIndexBits;
        blockSize = 1 << blockBits;
        wordSize = 4; // 4 bytes per word
        
        // Initialize cache sets
        for (int i = 0; i < sets; i++) {
            cacheSets.push_back(CacheSet(associativity, blockSize));
        }
    }
    
    // Extract tag, set index, and block offset from address
    void parseAddress(uint32_t address, uint32_t& tag, uint32_t& setIndex, uint32_t& blockOffset) {
        blockOffset = address & ((1 << blockBits) - 1);
        setIndex = (address >> blockBits) & ((1 << setIndexBits) - 1);
        tag = address >> (blockBits + setIndexBits);
    }
    
    // Get full address from tag, set index, and block offset
    uint32_t getFullAddress(uint32_t tag, uint32_t setIndex, uint32_t blockOffset) {
        return (tag << (blockBits + setIndexBits)) | (setIndex << blockBits) | blockOffset;
    }
    
    // Get block address (address with block offset bits set to 0)
    uint32_t getBlockAddress(uint32_t address) {
        return address & ~((1 << blockBits) - 1);
    }
    
    // Find a line in the cache set
    int findLine(uint32_t setIndex, uint32_t tag) {
        for (size_t i = 0; i < cacheSets[setIndex].lines.size(); i++) {
            if (cacheSets[setIndex].lines[i].valid && cacheSets[setIndex].lines[i].tag == tag) {
                return i;
            }
        }
        return -1; // Not found
    }
    
    // Update LRU counters for a cache set
    void updateLRU(uint32_t setIndex, int lineIndex) {
        uint32_t currentLRU = cacheSets[setIndex].lines[lineIndex].lru;
        for (auto& line : cacheSets[setIndex].lines) {
            if (line.valid && line.lru < currentLRU) {
                line.lru++;
            }
        }
        cacheSets[setIndex].lines[lineIndex].lru = 0;
    }
    
    // Find the LRU line in a cache set
    int getLRULine(uint32_t setIndex) {
        int lruIndex = 0;
        uint32_t maxLRU = cacheSets[setIndex].lines[0].lru;
        
        for (size_t i = 1; i < cacheSets[setIndex].lines.size(); i++) {
            if (!cacheSets[setIndex].lines[i].valid) {
                return i;
            }
            if (cacheSets[setIndex].lines[i].lru > maxLRU) {
                maxLRU = cacheSets[setIndex].lines[i].lru;
                lruIndex = i;
            }
        }
        
        return lruIndex;
    }
    
    // Check if an address is in the cache (in any valid state)
    bool isInCache(uint32_t address) {
        uint32_t tag, setIndex, blockOffset;
        parseAddress(address, tag, setIndex, blockOffset);
        
        int lineIndex = findLine(setIndex, tag);
        return (lineIndex != -1 && cacheSets[setIndex].lines[lineIndex].state != MESIState::INVALID);
    }
    
    // Get the MESI state of a line
    MESIState getLineState(uint32_t address) {
        uint32_t tag, setIndex, blockOffset;
        parseAddress(address, tag, setIndex, blockOffset);
        
        int lineIndex = findLine(setIndex, tag);
        if (lineIndex != -1) {
            return cacheSets[setIndex].lines[lineIndex].state;
        }
        return MESIState::INVALID;
    }
    
    // Set the state of a line
    void setLineState(uint32_t address, MESIState state) {
        uint32_t tag, setIndex, blockOffset;
        parseAddress(address, tag, setIndex, blockOffset);
        
        int lineIndex = findLine(setIndex, tag);
        if (lineIndex != -1) {
            cacheSets[setIndex].lines[lineIndex].state = state;
            // If becoming invalid, also mark as not valid
            if (state == MESIState::INVALID) {
                cacheSets[setIndex].lines[lineIndex].valid = false;
            }
        }
    }
    
    // Check if a line is dirty
    bool isLineDirty(uint32_t address) {
        uint32_t tag, setIndex, blockOffset;
        parseAddress(address, tag, setIndex, blockOffset);
        
        int lineIndex = findLine(setIndex, tag);
        return (lineIndex != -1 && cacheSets[setIndex].lines[lineIndex].dirty);
    }
    
    // Mark a line as dirty
    void setLineDirty(uint32_t address, bool dirty) {
        uint32_t tag, setIndex, blockOffset;
        parseAddress(address, tag, setIndex, blockOffset);
        
        int lineIndex = findLine(setIndex, tag);
        if (lineIndex != -1) {
            cacheSets[setIndex].lines[lineIndex].dirty = dirty;
        }
    }
    
    // Allocate a new line in the cache
    int allocateLine(uint32_t address, MESIState state, bool& eviction, uint32_t& evictedAddr, bool& writeback) {
        uint32_t tag, setIndex, blockOffset;
        parseAddress(address, tag, setIndex, blockOffset);
        
        // Check if the line already exists
        int lineIndex = findLine(setIndex, tag);
        if (lineIndex != -1) {
            cacheSets[setIndex].lines[lineIndex].state = state;
            cacheSets[setIndex].lines[lineIndex].valid = true;
            updateLRU(setIndex, lineIndex);
            eviction = false;
            writeback = false;
            return lineIndex;
        }
        
        // Find a line to allocate (either empty or LRU)
        lineIndex = -1;
        for (size_t i = 0; i < cacheSets[setIndex].lines.size(); i++) {
            if (!cacheSets[setIndex].lines[i].valid) {
                lineIndex = i;
                break;
            }
        }
        
        // If no empty line, use LRU
        if (lineIndex == -1) {
            lineIndex = getLRULine(setIndex);
            eviction = true;
            
            // Check if the evicted line is dirty (needs writeback)
            if (cacheSets[setIndex].lines[lineIndex].dirty && 
                cacheSets[setIndex].lines[lineIndex].state == MESIState::MODIFIED) {
                writeback = true;
                uint32_t evictedTag = cacheSets[setIndex].lines[lineIndex].tag;
                evictedAddr = getFullAddress(evictedTag, setIndex, 0); // Block address of evicted line
            } else {
                writeback = false;
            }
        } else {
            eviction = false;
            writeback = false;
        }
        
        // Initialize the new line
        cacheSets[setIndex].lines[lineIndex].tag = tag;
        cacheSets[setIndex].lines[lineIndex].state = state;
        cacheSets[setIndex].lines[lineIndex].valid = true;
        cacheSets[setIndex].lines[lineIndex].dirty = false;
        updateLRU(setIndex, lineIndex);
        
        return lineIndex;
    }
    
    // Get the data from a cache line
    std::vector<uint8_t> getLineData(uint32_t address) {
        uint32_t tag, setIndex, blockOffset;
        parseAddress(address, tag, setIndex, blockOffset);
        
        int lineIndex = findLine(setIndex, tag);
        if (lineIndex != -1) {
            return cacheSets[setIndex].lines[lineIndex].data;
        }
        // If not found, return an empty vector
        return std::vector<uint8_t>();
    }
    
    // Set the data in a cache line
    void setLineData(uint32_t address, const std::vector<uint8_t>& data) {
        uint32_t tag, setIndex, blockOffset;
        parseAddress(address, tag, setIndex, blockOffset);
        
        int lineIndex = findLine(setIndex, tag);
        if (lineIndex != -1 && data.size() == blockSize) {
            cacheSets[setIndex].lines[lineIndex].data = data;
        }
    }
    
    // Handle a bus transaction from another core
    bool handleBusTransaction(BusTransaction txType, uint32_t address, int sourceCoreId, 
                              std::vector<uint8_t>& data, GlobalStats& stats) {
        uint32_t tag, setIndex, blockOffset;
        parseAddress(address, tag, setIndex, blockOffset);
        
        int lineIndex = findLine(setIndex, tag);
        bool hasLine = (lineIndex != -1 && cacheSets[setIndex].lines[lineIndex].valid);
        
        if (!hasLine) {
            return false; // This cache doesn't have the line
        }
        
        MESIState currentState = cacheSets[setIndex].lines[lineIndex].state;
        
        switch (txType) {
            case BusTransaction::BUSRD:
                // Another core wants to read the line
                if (currentState == MESIState::MODIFIED) {
                    // Provide modified data to the requesting core and memory
                    data = cacheSets[setIndex].lines[lineIndex].data;
                    cacheSets[setIndex].lines[lineIndex].state = MESIState::SHARED;
                    cacheSets[setIndex].lines[lineIndex].dirty = false;
                    stats.dataTraffic += blockSize; // Data sent to both requestor and memory
                    return true;
                } else if (currentState == MESIState::EXCLUSIVE) {
                    // Change to shared state
                    cacheSets[setIndex].lines[lineIndex].state = MESIState::SHARED;
                    data = cacheSets[setIndex].lines[lineIndex].data;
                    stats.dataTraffic += blockSize; // Data sent to requestor
                    return true;
                } else if (currentState == MESIState::SHARED) {
                    // Already in shared state, provide data
                    data = cacheSets[setIndex].lines[lineIndex].data;
                    stats.dataTraffic += blockSize; // Data sent to requestor
                    return true;
                }
                break;
                
            case BusTransaction::BUSRDX:
                // Another core wants exclusive access
                if (currentState != MESIState::INVALID) {
                    // If we have the line, it must be invalidated
                    if (currentState == MESIState::MODIFIED) {
                        // Provide modified data
                        data = cacheSets[setIndex].lines[lineIndex].data;
                        stats.dataTraffic += blockSize; // Data sent to both requestor and memory
                    }
                    cacheSets[setIndex].lines[lineIndex].state = MESIState::INVALID;
                    cacheSets[setIndex].lines[lineIndex].valid = false;
                    stats.invalidations++;
                    return (currentState == MESIState::MODIFIED);
                }
                break;
                
            case BusTransaction::INVALIDATE:
                // Another core wants to invalidate this line
                if (currentState != MESIState::INVALID) {
                    cacheSets[setIndex].lines[lineIndex].state = MESIState::INVALID;
                    cacheSets[setIndex].lines[lineIndex].valid = false;
                    stats.invalidations++;
                }
                break;
                
            default:
                break;
        }
        
        return false;
    }
};

// Core Class
class Core {
private:
    int id;
    Cache cache;
    std::ifstream traceFile;
    std::string currentOp;
    uint32_t currentAddr;
    bool hasNextOp;
    bool waitingForMemory;
    int waitCycles;
    CoreStats stats;
    
public:
    Core(int coreId, int s, int E, int b, const std::string& tracePath)
        : id(coreId), cache(coreId, s, E, b), waitingForMemory(false), waitCycles(0) {
        
        traceFile.open(tracePath);
        if (!traceFile.is_open()) {
            std::cerr << "Error opening trace file: " << tracePath << std::endl;
            exit(1);
        }
        
        // Read the first operation
        hasNextOp = getNextOp();
    }
    
    ~Core() {
        if (traceFile.is_open()) {
            traceFile.close();
        }
    }
    
    // Get the next operation from the trace file
    bool getNextOp() {
        std::string line;
        if (std::getline(traceFile, line)) {
            std::istringstream iss(line);
            iss >> currentOp >> currentAddr;
            
            // Convert hex string to uint32_t
            if (currentAddr.substr(0, 2) == "0x") {
                currentAddr = currentAddr.substr(2);
            }
            std::stringstream ss;
            ss << std::hex << currentAddr;
            ss >> std::hex >> currentAddr;
            
            return true;
        }
        return false;
    }
    
    // Process the current operation
    bool processCurrentOp(std::queue<BusRequest>& busQueue, int currentCycle) {
        if (!hasNextOp || waitingForMemory) {
            return false;
        }
        
        uint32_t address = currentAddr;
        bool isRead = (currentOp == "R");
        
        if (isRead) {
            stats.readCount++;
            return processRead(address, busQueue, currentCycle);
        } else { // Write
            stats.writeCount++;
            return processWrite(address, busQueue, currentCycle);
        }
    }
    
    // Process a read operation
    bool processRead(uint32_t address, std::queue<BusRequest>& busQueue, int currentCycle) {
        stats.accesses++;
        
        uint32_t tag, setIndex, blockOffset;
        cache.parseAddress(address, tag, setIndex, blockOffset);
        
        int lineIndex = cache.findLine(setIndex, tag);
        if (lineIndex != -1) {
            // Cache hit
            MESIState state = cache.getLineState(address);
            if (state != MESIState::INVALID) {
                // Valid hit
                cache.updateLRU(setIndex, lineIndex);
                stats.totalCycles += 1; // L1 hit takes 1 cycle
                hasNextOp = getNextOp(); // Move to next operation
                return true;
            }
        }
        
        // Cache miss
        stats.misses++;
        
        // Add a bus read request
        busQueue.push(BusRequest(id, BusTransaction::BUSRD, cache.getBlockAddress(address), currentCycle));
        
        // Wait for the memory access to complete
        waitingForMemory = true;
        waitCycles = 0; // Will be set by the bus controller
        
        return true;
    }
    
    // Process a write operation
    bool processWrite(uint32_t address, std::queue<BusRequest>& busQueue, int currentCycle) {
        stats.accesses++;
        
        uint32_t tag, setIndex, blockOffset;
        cache.parseAddress(address, tag, setIndex, blockOffset);
        
        int lineIndex = cache.findLine(setIndex, tag);
        if (lineIndex != -1) {
            // Cache hit
            MESIState state = cache.getLineState(address);
            if (state == MESIState::MODIFIED || state == MESIState::EXCLUSIVE) {
                // Can write directly
                cache.setLineState(address, MESIState::MODIFIED);
                cache.setLineDirty(address, true);
                cache.updateLRU(setIndex, lineIndex);
                stats.totalCycles += 1; // L1 hit takes 1 cycle
                hasNextOp = getNextOp(); // Move to next operation
                return true;
            } else if (state == MESIState::SHARED) {
                // Need to get exclusive access first
                busQueue.push(BusRequest(id, BusTransaction::BUSRDX, cache.getBlockAddress(address), currentCycle));
                waitingForMemory = true;
                waitCycles = 0; // Will be set by the bus controller
                return true;
            }
        }
        
        // Cache miss
        stats.misses++;
        
        // Add a bus read exclusive request
        busQueue.push(BusRequest(id, BusTransaction::BUSRDX, cache.getBlockAddress(address), currentCycle));
        
        // Wait for the memory access to complete
        waitingForMemory = true;
        waitCycles = 0; // Will be set by the bus controller
        
        return true;
    }
    
    // Complete a memory operation after the bus transaction
    void completeMemoryOp(MESIState newState, const std::vector<uint8_t>& data, uint32_t address, bool isWrite) {
        bool eviction = false;
        bool writeback = false;
        uint32_t evictedAddr = 0;
        
        // Allocate a line in the cache
        cache.allocateLine(address, newState, eviction, evictedAddr, writeback);
        
        // Update data if provided
        if (!data.empty()) {
            cache.setLineData(address, data);
        }
        
        // If this was a write, mark the line as dirty
        if (isWrite) {
            cache.setLineDirty(address, true);
            cache.setLineState(address, MESIState::MODIFIED);
        }
        
        // Update statistics
        if (eviction) {
            stats.evictions++;
        }
        if (writeback) {
            stats.writebacks++;
        }
        
        // Ready for the next operation
        waitingForMemory = false;
        hasNextOp = getNextOp();
    }
    
    // Simulate a cycle of execution
    void simulateCycle(int currentCycle) {
        stats.totalCycles = currentCycle;
        
        if (waitingForMemory) {
            stats.idleCycles++;
            if (waitCycles > 0) {
                waitCycles--;
            }
        }
    }
    
    // Check if the core is waiting for a memory operation
    bool isWaiting() const {
        return waitingForMemory;
    }
    
    // Set the wait cycles for a memory operation
    void setWaitCycles(int cycles) {
        waitCycles = cycles;
    }
    
    // Check if the core has completed all operations
    bool isDone() const {
        return !hasNextOp && !waitingForMemory;
    }
    
    // Get the cache for this core
    Cache& getCache() {
        return cache;
    }
    
    // Get the stats for this core
    const CoreStats& getStats() const {
        return stats;
    }
    
    // Handle a completed bus transaction
    void handleCompletedBusTransaction(uint32_t address, MESIState newState, 
                                      const std::vector<uint8_t>& data, bool isWrite) {
        if (waitingForMemory && cache.getBlockAddress(currentAddr) == cache.getBlockAddress(address)) {
            completeMemoryOp(newState, data, cache.getBlockAddress(address), isWrite);
        }
    }
};

// Bus Controller Class
class BusController {
private:
    std::vector<Core>& cores;
    std::queue<BusRequest>& busQueue;
    GlobalStats& stats;
    bool busLocked;
    int currentReqCycles;
    BusRequest* currentRequest;
    
    std::vector<uint8_t> memoryData; // Simulated memory data (for simplicity)
    
public:
    BusController(std::vector<Core>& c, std::queue<BusRequest>& queue, GlobalStats& s)
        : cores(c), busQueue(queue), stats(s), busLocked(false), currentReqCycles(0), 
          currentRequest(nullptr) {
        
        // Initialize memory (for simulation)
        memoryData.resize(1024, 0); // Simple stub memory
    }
    
    // Process a bus cycle
    void processBusCycle() {
        if (busLocked) {
            currentReqCycles--;
            if (currentReqCycles <= 0) {
                // Request completed
                completeBusTransaction();
                busLocked = false;
                delete currentRequest;
                currentRequest = nullptr;
            }
            return;
        }
        
        if (busQueue.empty()) {
            return;
        }
        
        // Start a new bus transaction
        currentRequest = new BusRequest(busQueue.front());
        busQueue.pop();
        
        busLocked = true;
        beginBusTransaction();
    }
    
    // Begin a bus transaction
    void beginBusTransaction() {
        uint32_t address = currentRequest->address;
        int requestingCore = currentRequest->coreId;
        BusTransaction txType = currentRequest->type;
        
        switch (txType) {
            case BusTransaction::BUSRD: {
                // Check if any other cache has the line
                bool foundInOtherCache = false;
                std::vector<uint8_t> data;
                
                for (size_t i = 0; i < cores.size(); i++) {
                    if (i != requestingCore) {
                        if (cores[i].getCache().handleBusTransaction(BusTransaction::BUSRD, address, 
                                                                   requestingCore, data, stats)) {
                            foundInOtherCache = true;
                            break;
                        }
                    }
                }
                
                if (foundInOtherCache) {
                    // Get data from other cache
                    int words = data.size() / 4; // Number of words (4 bytes each)
                    currentReqCycles = 2 * words; // 2 cycles per word
                } else {
                    // Get data from memory
                    currentReqCycles = 100; // Memory access takes 100 cycles
                }
                break;
            }
            
            case BusTransaction::BUSRDX: {
                // Check if any other cache has the line
                bool foundInOtherCache = false;
                std::vector<uint8_t> data;
                
                for (size_t i = 0; i < cores.size(); i++) {
                    if (i != requestingCore) {
                        if (cores[i].getCache().handleBusTransaction(BusTransaction::BUSRDX, address, 
                                                                   requestingCore, data, stats)) {
                            foundInOtherCache = true;
                            // Note: We continue looking at other caches to invalidate their copies
                        }
                    }
                }
                
                if (foundInOtherCache) {
                    // Get data from other cache and invalidate all copies
                    int words = data.size() / 4; // Number of words (4 bytes each)
                    currentReqCycles = 2 * words; // 2 cycles per word
                } else {
                    // Get data from memory
                    currentReqCycles = 100; // Memory access takes 100 cycles
                }
                break;
            }
            
            case BusTransaction::FLUSH: {
                // Write back dirty data to memory
                currentReqCycles = 100; // Memory write takes 100 cycles
                break;
            }
            
            case BusTransaction::INVALIDATE: {
                // Invalidate all copies in other caches
                for (size_t i = 0; i < cores.size(); i++) {
                    if (i != requestingCore) {
                        std::vector<uint8_t> dummy;
                        cores[i].getCache().handleBusTransaction(BusTransaction::INVALIDATE, address, 
                                                               requestingCore, dummy, stats);
                    }
                }
                currentReqCycles = 1; // Invalidation is quick
                break;
            }
            
            default:
                break;
        }
        
        // Set the wait cycles for the requesting core
        cores[requestingCore].setWaitCycles(currentReqCycles);
    }
    
    // Complete a bus transaction
    void completeBusTransaction() {
        uint32_t address = currentRequest->address;
        int requestingCore = currentRequest->coreId;
        BusTransaction txType = currentRequest->type;
        
        // Prepare data for the completed transaction
        std::vector<uint8_t> data;
        data.resize(cores[0].getCache().getBlockSize(), 0); // Placeholder data
        
        switch (txType) {
            case BusTransaction::BUSRD: {
                // Read completed - update the requesting core's cache
                cores[requestingCore].handleCompletedBusTransaction(
                    address, MESIState::SHARED, data, false);
                break;
            }
            
            case BusTransaction::BUSRDX: {
                // Read-exclusive completed - update the requesting core's cache
                cores[requestingCore].handleCompletedBusTransaction(
                    address, MESIState::EXCLUSIVE, data, true);
                break;
            }
            
            case BusTransaction::FLUSH: {
                // Flush completed - nothing more to do
                break;
            }
            
            case BusTransaction::INVALIDATE: {
                // Invalidation completed - nothing more to do
                break;
            }
            
            default:
                break;
        }
    }
    
    // Check if the bus is locked (busy with a transaction)
    bool isBusLocked() const {
        return busLocked;
    }
};

// Simulator Class
class CacheSimulator {
private:
    int setIndexBits;
    int associativity;
    int blockBits;
    std::string tracePrefix;
    std::string outputFileName;
    
    std::vector<Core> cores;
    std::queue<BusRequest> busQueue;
    GlobalStats globalStats;
    BusController busController;
    
    int currentCycle;
    
public:
    CacheSimulator(int s, int E, int b, const std::string& tPrefix, const std::string& outFile)
        : setIndexBits(s), associativity(E), blockBits(b), tracePrefix(tPrefix), 
          outputFileName(outFile), busController(cores, busQueue, globalStats), currentCycle(0) {
        
        // Initialize cores with their trace files
        for (int i = 0; i < 4; i++) {
            std::string tracePath = tracePrefix + "_proc" + std::to_string(i) + ".trace";
            cores.push_back(Core(i, setIndexBits, associativity, blockBits, tracePath));
        }
    }
    
    // Run the simulation
    void run() {
        bool allDone = false;
        
        while (!allDone) {
            currentCycle++;
            
            // Process each core's operation for this cycle
            for (size_t i = 0; i < cores.size(); i++) {
                cores[i].simulateCycle(currentCycle);
                if (!cores[i].isWaiting() && !cores[i].isDone()) {
                    cores[i].processCurrentOp(busQueue, currentCycle);
                }
            }
            
            // Process bus operations
            busController.processBusCycle();
            
            // Check if all cores are done
            allDone = true;
            for (const auto& core : cores) {
                if (!core.isDone()) {
                    allDone = false;
                    break;
                }
            }
        }
        
        // Output the results
        outputResults();
    }
    
    // Output the simulation results
    void outputResults() {
        std::ofstream outFile;
        if (!outputFileName.empty()) {
            outFile.open(outputFileName);
            if (!outFile.is_open()) {
                std::cerr << "Error opening output file: " << outputFileName << std::endl;
                return;
            }
        }
        
        std::ostream& out = outputFileName.empty() ? std::cout : outFile;
        
        out << "Simulation Results:" << std::endl;
        out << "------------------" << std::endl;
        out << "Cache Configuration: " << (1 << setIndexBits) * associativity * (1 << blockBits) / 1024 
            << "KB, " << associativity << "-way, " << (1 << blockBits) << "-byte blocks" << std::endl;
        out << std::endl;
        
        for (size_t i = 0; i < cores.size(); i++) {
            const CoreStats& stats = cores[i].getStats();
            out << "Core " << i << ":" << std::endl;
            out << "  Instructions: " << (stats.readCount + stats.writeCount) 
                << " (" << stats.readCount << " reads, " << stats.writeCount << " writes)" << std::endl;
            out << "  Total cycles: " << stats.totalCycles << std::endl;
            out << "  Idle cycles: " << stats.idleCycles << std::endl;
            out << "  Miss rate: " << std::fixed << std::setprecision(6) 
                << (double)stats.misses / stats.accesses * 100 << "%" << std::endl;
            out << "  Evictions: " << stats.evictions << std::endl;
            out << "  Writebacks: " << stats.writebacks << std::endl;
            out << std::endl;
        }
        
        out << "Global statistics:" << std::endl;
        out << "  Invalidations: " << globalStats.invalidations << std::endl;
        out << "  Bus traffic: " << globalStats.dataTraffic << " bytes" << std::endl;
        
        if (outFile.is_open()) {
            outFile.close();
        }
    }
    
    // Get maximum execution time across cores
    int getMaxExecutionTime() const {
        int maxTime = 0;
        for (const auto& core : cores) {
            maxTime = std::max(maxTime, core.getStats().totalCycles);
        }
        return maxTime;
    }
};

void printUsage(const char* programName) {
    std::cout << "Usage: " << programName << " [options]" << std::endl;
    std::cout << "Options:" << std::endl;
    std::cout << "  -t <tracefile>: name of parallel application (e.g. app1) whose 4 traces are to be used" << std::endl;
    std::cout << "  -s <s>: number of set index bits (number of sets in the cache = 2^s)" << std::endl;
    std::cout << "  -E <E>: associativity (number of cache lines per set)" << std::endl;
    std::cout << "  -b <b>: number of block bits (block size = 2^b)" << std::endl;
    std::cout << "  -o <outfilename>: logs output in file for plotting etc." << std::endl;
    std::cout << "  -h: prints this help" << std::endl;
}

int main(int argc, char* argv[]) {
    int s = 6;  // Default: 64 sets (6 bits)
    int E = 2;  // Default: 2-way associative
    int b = 5;  // Default: 32 bytes per block (5 bits)
    std::string tracePrefix = "app1";
    std::string outputFileName = "";
    
    // Parse command line arguments
    int opt;
    while ((opt = getopt(argc, argv, "t:s:E:b:o:h")) != -1) {
        switch (opt) {
            case 't':
                tracePrefix = optarg;
                break;
            case 's':
                s = std::stoi(optarg);
                break;
            case 'E':
                E = std::stoi(optarg);
                break;
            case 'b':
                b = std::stoi(optarg);
                break;
            case 'o':
                outputFileName = optarg;
                break;
            case 'h':
                printUsage(argv[0]);
                return 0;
            default:
                printUsage(argv[0]);
                return 1;
        }
    }
    
    // Print configuration
    std::cout << "Running cache simulator with the following configuration:" << std::endl;
    std::cout << "  Trace prefix: " << tracePrefix << std::endl;
    std::cout << "  Number of set index bits (s): " << s << std::endl;
    std::cout << "  Associativity (E): " << E << std::endl;
    std::cout << "  Number of block bits (b): " << b << std::endl;
    std::cout << "  Output file: " << (outputFileName.empty() ? "stdout" : outputFileName) << std::endl;
    
    // Create and run the simulator
    CacheSimulator simulator(s, E, b, tracePrefix, outputFileName);
    simulator.run();
    
    return 0;
}
