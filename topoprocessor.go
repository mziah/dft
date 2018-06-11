/*********************************************************
	Min Weight Topology Computation RPC Service
	Calculates all pair Min Weight Topology from a source,
	Minimum Spanning Tree or Shrtest path Tree,
	Shortest ECMP paths
	ECMP Next Hops from a source to a destination

	Version 0.1

	Author: Masum Z. Hasan 2017-2018
**********************************************************/

package main

import (
	"bytes"
	"encoding/json"
	"errors"
	"fmt"
	"io/ioutil"
	"log"
	"net"
	"net/rpc"
	"os"
	"reflect"
	"strconv"
	"time"
)

// For JSON
const (
	empty = ""
	tab   = "\t"
)

/**************************************************************************************
	Meta info for Gatekeeper, Computation, Micro-VNF, Blockchain, NUMA Host Resource Control
	and other Services (should be in shared folder)
***************************************************************************************/

type ServiceInfo struct {
	// Go RPC name should be capitalized for it to be exported
	// K8s DNS convention require all lowercase name
	// Hence name and RPC name
	ServiceName    string `json:"ServiceName"`
	ServiceRPCName string `json:"ServiceRPCName,omitempty"`
	// Methods that the service implements
	ServiceMethods    []string `json:"ServiceMethods,omitempty"`
	ServiceIP         string   `json:"ServiceIP"` // IP address
	ServicePort       string   `json:"ServicePort"`
	ServiceMapper     string   `json:"ServiceMapper,omitempty"`
	ServiceMapperPort string   `json:"ServiceMapperPort,omitempty"` // used by other services
	Replica           int      `json:"Replica,omitempty"`
	NameSpace         string   `json:"NameSpace,omitempty"`
	ClusterDomain     string   `json:"ClusterDomain,omitempty"`
	// DNS domain name
	ServiceInstance string `json:"ServiceInstance,omitempty"`
	// Above is service address, following is IP address of a Network Node like Micro-VNF
	NetNodeID     string `json:"NetNodeID,omitempty"`
	ServiceStatus int    `json:"ServiceStatus,omitempty"` // 2: up, 0: down, 1: transition
	pss           int    // Previous status
	// Info about how much info this server carry (ex. ServiceMap size or Graph size)
	// Should be a struct
	ServiceKnowledge interface{} `json:"ServiceKnowledge,omitempty"`
	// ServiceKnowledge is key-value pair, examples:
	// MVNF: TNodeID, <ip address of node> (not service IP), TNodes, <#>, TEdges, <#>
	// MWT: TNodes, <#>, TEdges, <#>
	//ServiceKnowledge []string `json:"ServiceKnowledge,omitempty"`
	// Can serve multiple regions, ALL for no specific region
	ServiceRegion []string    `json:"ServiceRegion,omitempty"`
	psn           interface{} // previous ServiceKnowledge
	//psn               []string    // previous ServiceKnowledge
	ServiceLaunchTime interface{} `json:"ServiceLaunchime,omitempty"`
	//ServiceUpdateTime time.Time   `json:"ServiceUpdateTime,omitempty"`
	ServiceUpdateTime interface{} `json:"ServiceUpdateTime,omitempty"`
}

var ServiceMap map[string][]ServiceInfo

// Config parameters
type MWTParams struct {
	ServicePingInterval string `json:"ServicePingInterval"`
}

var PingInt time.Duration = 2 * time.Second

var ThisNodeIP string
var ThisNodeName string

var NodeToID map[string]string

/**************************************************************************************
	For MicroVNF
***************************************************************************************/

// Topology: used for update -- this is converted to another topology (graph) structure
// developed earlier for all node shortest weight graph computation
// This is modeled in a way so that incremental updates can be sent

type TopoNode struct {
	Name string `json:"Name"`
	ID   string `json:"ID"` // IP or MAC or ...
	//Status   string `json:"Status,omitempty"`
	MicroVNF bool   `json:"MicroVNF"`
	Function string `json:"Function,omitempty"` // Shortest Path / ECMP Forwarder mVNF, BGP, etc.
	Idx      int    // TO make compatible with Min Weight Topology implementation
}

type TopoNeighbor struct {
	ThisNodeID   string `json:"ThisNodeID"` // IP or MAC or ...
	ThisNodeName string `json:"ThisNodeName"`
	NeighborID   string `json:"NeighborIP"`
	NeighborName string `json:"NeighborName"`
	//EdgeStatus string `json:"EdgeStatus,omitempty"`
	EdgeWeight int  `json:"EdgeWeight"`
	MicroVNF   bool `json:"MicroVNF"` // Neighbor is leaf or MicroVNF
}

type Topology struct {
	ThisNode  TopoNode
	Neighbors []TopoNeighbor
}

type PathRequest struct {
	src string
	dst string
}

// Map on Node IP address to Topology
var InitialTopology map[string]*Topology
var PrevInitialTopology map[string]*Topology

// Neighbors that are not active yet as MVNF node
var PendingNB map[string][]TopoNeighbor

//var DeletedNodes map[string]*Topology

/**************************************************************************************
	TopoProcessor variables, structs
***************************************************************************************/

// In min weight topology  or minimum spanning tree computation a node is represented
// with an interger, not IP address, which is mapped to IDX
var IDX int

// const should be read from configuration files
// BIGNUMBER : : For Shortest path weight calc
const BIGNUMBER = 99999999

// Should be variabl with slice append
const NECMP = 10 // # of ECMP supported

// NUMNODES : :
var NUMNODES int

// NUMEDGES : :
var NUMEDGES int

// NodesVisited : : Used in Breadth first traversal to exit recursion
var NodesVisited int

// Edge : :
type Edge struct {
	id     int
	ip     string
	src    int    // Node id
	dst    int    // Node id
	srcip  string // IP
	dstip  string
	srcnm  string // Name
	dstnm  string
	params int  // can be multivariate like BW, delay, jitter and/or colors; we'll use it as weight
	spt    bool // Is this edge part of SPT?
}

// Node : :
type Node struct {
	id       int
	ip       string     // IP address from InitialTopology key
	nm       string     // Name
	aedges   []int      // ids array of adjacent edges
	nedges   int        // # of adjacent edges
	params   int        // sum of shortest path weight from source to this node
	lpr      bool       // Previous lower param replaced - to keep track of ECMP
	sptedge  [NECMP]int // Id of the edge leading to shortest path weight; Array for 10 ECMP
	nsptedge int        // current count of sptedge
	visited  bool
	addedMH  bool // Added to MinHeapSet
}

// Graph : :
type Graph struct {
	nodes []Node
	edges []Edge
}

// MinHeap : :
type MinHeap struct {
	// Idx of Node
	Idx   int
	value int
}

// CurrentSize : : Used in Min Heap
var CurrentSize = 0

// Leaf node or prefix reachable via next hop from this node
type NextHopToLeaf struct {
	LeafNodeID string
	Idx        int
	// Leaf reachable via multiple (ECMP) next hops
	//NextHops []NextHop
	NextHops map[string]*NextHop
}

type NextHop struct {
	//IP     string
	Weight int
	Idx    int
}

type NextHopToLeafCP struct {
	LeafNodeID string
	// Leaf reachable via multiple (ECMP) next hops
	NextHops []NextHopCP
	Deleted  bool
}

type NextHopCP struct {
	IP      string
	Weight  int
	Deleted bool
}

//var NHop2Leaves map[string]*NextHopToLeaf
// Leaf Name --> Next Hop Name --> Weight
var NHop2Leaves map[string]map[string]int

// Leaf ID --> Next Hop ID --> Weight
var NHop2LeavesID map[string]map[string]int

// Leaf --> Idx
var Leaves map[string]int

type NHopInfo struct {
	NL map[string]map[string]int
	LF map[string]int
}

//var DeletedNodes map[string]bool

type TopologyStates struct {
	InitialTopology map[string]*Topology
	PendingNB       map[string][]TopoNeighbor
	//NHop2Leaves     map[string]*NextHopToLeaf
	NHop2Leaves map[string]map[string]int
	Leaves      map[string]int
	IDX         int
}

var TopoStates TopologyStates

var DeleteList map[string]bool

type TopoProcessor struct {
}

/**************************************************************************************
	UTILITY FUNCTIONS (should go in shared folder)
***************************************************************************************/

// IP of Container
// From external source - modify later
func GetIPv4() (string, error) {
	ifs, err := net.Interfaces()
	if err != nil {
		return "", err
	}
	for _, intf := range ifs {
		if intf.Flags&net.FlagUp == 0 {
			continue // intf down
		}
		if intf.Flags&net.FlagLoopback != 0 {
			continue // lo
		}
		addrs, err := intf.Addrs()
		if err != nil {
			return "", err
		}
		for _, addr := range addrs {
			var ip net.IP
			switch v := addr.(type) {
			case *net.IPNet:
				ip = v.IP
			case *net.IPAddr:
				ip = v.IP
			}
			if ip == nil || ip.IsLoopback() {
				continue
			}
			ip = ip.To4()
			if ip == nil {
				continue // not an ipv4 address
			}
			return ip.String(), nil
		}
	}
	return "", errors.New("No Network connection")
}

// Get available port, if dynamic port use turned on
func GetPort() (string, error) {

	l, err := net.Listen("tcp", "127.0.0.1:0")

	l.Close()

	// host
	h := l.Addr().String()

	// Split the host from the port
	_, p, err := net.SplitHostPort(h)

	return p, err
}

func ReadFromFile(filename string) []byte {
	file, err := ioutil.ReadFile(filename)
	if err != nil {
		fmt.Printf("Cannot read file %s: %s\n", filename, err)
		os.Exit(1)
		//panic(err)
		//check(err)
	}
	return file
}

func WriteFiles(filename string, data []byte) {
	err := ioutil.WriteFile(filename, data, 0644)
	//check(err)
	if err != nil {
		fmt.Printf("Cannot Write file %s: %s\n", filename, err)
		os.Exit(1)
	}
}

func LocalTimeMs() string {

	t := time.Now()
	z, _ := t.In(time.Local).Zone()
	tf := t.Format("01/02/2006 03:04:05.000 PM")

	tt := fmt.Sprintf("%s %s", tf, z)

	return tt
}

// m: Extra message to print
func PrettyPrintJSON(in interface{}, m string) {

	// Add log

	r, err := json.Marshal(in)
	if err != nil {
		log.Fatal(err)
	}
	var prettyJSON bytes.Buffer
	error := json.Indent(&prettyJSON, r, empty, tab)
	if error != nil {
		fmt.Println("JSON ERROR")
		return
	}

	fmt.Printf("%s: \n %s\n %s\n", m, LocalTimeMs(), string(prettyJSON.Bytes()))

}

// f: file to read, m: extra message to print in Pretty JSON
func ReadJSONInfo(f, m string) ServiceInfo {

	fl := ReadFromFile(f)
	fmt.Printf("%s:\n %s\n", m, string(fl))
	//PrettyPrintJSON(fl, m)

	si := ServiceInfo{}
	json.Unmarshal([]byte(string(fl)), &si)
	//fmt.Println(si)

	return si

}

/**************************************************************************************
	Min Weight Topology computation related
***************************************************************************************/

func initMinHeap(Idx int) []MinHeap {

	//fmt.Printf("InitMinHeap NUMNODES %d\n", NUMNODES)

	MinHeapSet := make([]MinHeap, NUMNODES)
	for _, v := range InitialTopology {
		i := v.ThisNode.Idx
		MinHeapSet[i].value = BIGNUMBER
		MinHeapSet[i].Idx = i
	}

	// Source node
	MinHeapSet[0].value = 0
	MinHeapSet[0].Idx = Idx
	CurrentSize = 1

	return MinHeapSet
}

// Stacki : : Stack with integer
type Stacki struct {
	value []int // Will contain index to Nodes
	count int
}

func (s *Stacki) Push(value int) {

	// Memory allocated fixed amount (in main) when Stacki created
	// Increase slice ([]value) size 3 times (in anticipation of stack growth), when count increases and more value pushed
	if s.count > len(s.value) {
		v := make([]int, len(s.value)*10)
		// copy existing stack value to newly allocated memory pointed to by v
		copy(v, s.value)
		// It now point to new memory
		s.value = v
	}
	// Push value into stack
	//fmt.Printf("****s.count = %d****\n", s.count)
	s.value[s.count] = value
	s.count++

}

func (s *Stacki) Pop() int {
	if s.count == 0 {
		return 0
	}
	v := s.value[s.count-1]
	s.count--
	return v
}

// FifoQ : :
type FifoQi struct {
	value []int // Will contain index to Nodes
	head  int
	tail  int
	count int
}

func (q *FifoQi) Push(value int) {

	// Memory allocated fixed amount (in main) when FifoQi created
	// Increase slice ([]value) size 3 times (in anticipation of Q growth),
	// when count increases beyond current Q length and more value pushed
	if q.count == len(q.value) {
		v := make([]int, len(q.value)*3)
		// copy existing Q contents from head to end to newly allocated memory pointed to by v
		copy(v, q.value[q.head:])
		// It now points to new memory
		q.value = v
		q.head = 0
		q.tail = len(q.value)
	}
	// Add value at tail
	q.value[q.tail] = value
	//q.tail = (q.tail + 1) % len(q.value)
	q.tail = q.tail + 1

	q.count++
}

func (q *FifoQi) Pop() int {
	if q.count == 0 {
		return 0
	}
	v := q.value[q.head]
	//q.head = (q.head + 1) % len(q.value)
	q.head = q.head + 1
	q.count--
	return v
}

// Total # of active edges in the topology
func totalEdges() int {
	var numEdges = 0
	for _, v := range InitialTopology {
		numEdges += len(v.Neighbors)
	}
	return numEdges
}

// Total # of active nodes in the topology
func totalNodes() int {

	return len(InitialTopology)
}

// # if edges in a given node
func numEdgesInNode(v []TopoNeighbor) int {

	return len(v)

}

// Delete an element in slice by preserving order - move elements to left
func deleteNeighbor1(n []TopoNeighbor, i int) []TopoNeighbor {
	return append(n[:i], n[i+1:]...)
}

// Delete by swapping last element with the deleted one
//func deleteNeighbor2(n []NeighborInfo, i int) []NeighborInfo {
func deleteNeighbor2(n []TopoNeighbor, i int) []TopoNeighbor {

	//n[len(n)-1], n[i] = n[i], n[len(n)-1]
	n[i] = n[len(n)-1]
	return n[:len(n)-1]
}

func printStructWithField(t *Graph) {

	s := reflect.ValueOf(t).Elem()
	typeOfT := s.Type()

	for i := 0; i < s.NumField(); i++ {
		f := s.Field(i)
		fmt.Printf("%s = %v\n",
			//typeOfT.Field(i).Name, f.Type(), f.Interface())
			typeOfT.Field(i).Name, f.Interface())
	}
}

func PrintInitialTopology() {

	for k, v := range InitialTopology {
		fmt.Printf("%s  %d\n", k, v.ThisNode.Idx)
		n := v.Neighbors
		for i := range n {
			fmt.Printf("     %s %s %t %d\n", n[i].ThisNodeID, n[i].NeighborID, n[i].MicroVNF, n[i].EdgeWeight)
		}
		fmt.Println()
	}
}

// Initialize the Graph / topology
func initGraph() *Graph {

	//fmt.Printf("Main Topology\n")
	//PrintInitialTopology()

	NUMNODES = totalNodes()
	NUMEDGES = totalEdges()

	fmt.Printf("TNodes = %d TEdges =  %d\n", NUMNODES, NUMEDGES)

	if NUMNODES <= 1 {
		return nil
	}

	if NUMEDGES == 0 {
		return nil
	}

	gr := new(Graph)
	gr.nodes = make([]Node, NUMNODES)
	gr.edges = make([]Edge, NUMEDGES)
	// Create Nodes
	for k, v := range InitialTopology {
		if v != nil {
			//fmt.Printf("initGraph: NODE %s\n", v.ThisNode.ID)
			i := v.ThisNode.Idx // To take care of issue that map ranges over randomly
			gr.nodes[i].id = i
			gr.nodes[i].ip = v.ThisNode.ID
			gr.nodes[i].nm = k
			gr.nodes[i].params = BIGNUMBER
			ne := numEdgesInNode(v.Neighbors)
			gr.nodes[i].aedges = make([]int, ne)
			gr.nodes[i].nedges = ne
			gr.nodes[i].visited = false
			gr.nodes[i].addedMH = false
			gr.nodes[i].lpr = false
			gr.nodes[i].nsptedge = 0
			for j := 0; j < NECMP; j++ {
				gr.nodes[i].sptedge[j] = BIGNUMBER
			}
			i++
		}
	}
	// Create Edges; All Nodes should be created already
	// l: for all the edges in graph
	l := 0
	// n: edges per node
	n := 0
	for _, v := range InitialTopology { // ranges over randomly
		if v != nil {
			k := v.ThisNode.Idx
			for j := range v.Neighbors { // j ranges over slice - not randomized
				//if v.Neighbors[j].EdgeStatus == "on" {
				// Edges attached to nodes
				// Neighbor IP can be specified in config of this node
				// But Neighbor IP may not exist in InitialTopology
				// Then don't add edge
				//nid := v.Neighbors[j].NeighborID
				nid := v.Neighbors[j].NeighborName
				nbr := InitialTopology[nid]
				if nbr != nil {
					gr.edges[l].id = l
					gr.edges[l].src = k
					gr.edges[l].srcip = v.ThisNode.ID
					gr.edges[l].srcnm = v.ThisNode.Name
					d := nbr.ThisNode.Idx
					gr.edges[l].dst = d
					gr.edges[l].dstip = v.Neighbors[j].NeighborID
					gr.edges[l].dstnm = v.Neighbors[j].NeighborName
					gr.edges[l].params = v.Neighbors[j].EdgeWeight
					gr.edges[l].spt = false

					gr.nodes[k].aedges[n] = l

					n++
					l++
				}
			}
			n = 0
		}
	}
	return gr
}

// Create Min Heap of Topology node weight for Min Weight Topology computation
func createMinHeapNodeWeight(MinHeapSet []MinHeap, rootIdx int) {

	idxOfSmallerChild := rootIdx
	// In a binary tree at level l there are 2^l (^  : power) elements
	// If index of 1st element at level l is n, then last element index will be 2*n
	// Hence index of children at level l+1 of an index (root) n at level l will be 2*n+1 (left child) and 2*n+2 (right child)
	leftIdx := 2*rootIdx + 1
	rightIdx := 2*rootIdx + 2

	// leftIdx or rightIdx < listSize check: any index (node) > list size will not have child (as element at that index non-existent)
	// Will check nil if represented as struct

	if leftIdx < CurrentSize && MinHeapSet[leftIdx].value < MinHeapSet[idxOfSmallerChild].value {
		idxOfSmallerChild = leftIdx
	}
	if rightIdx < CurrentSize && MinHeapSet[rightIdx].value < MinHeapSet[idxOfSmallerChild].value {
		idxOfSmallerChild = rightIdx
	}

	// Index (idxOfSmallerChild) of smaller child identified
	// Now swap this child with parent, if they are not the same

	if idxOfSmallerChild != rootIdx {

		tempv := MinHeapSet[rootIdx].value
		tempi := MinHeapSet[rootIdx].Idx
		MinHeapSet[rootIdx].value = MinHeapSet[idxOfSmallerChild].value
		MinHeapSet[rootIdx].Idx = MinHeapSet[idxOfSmallerChild].Idx
		MinHeapSet[idxOfSmallerChild].value = tempv
		MinHeapSet[idxOfSmallerChild].Idx = tempi

		// Debug
		//printMinHeap(list)

		// Now resursively push parent down the heap because it is a larger valur and move smaller value up
		createMinHeapNodeWeight(MinHeapSet, idxOfSmallerChild)
	}
}

// Extract min from heap, then adjust heap -- list is sorted if called list size-1 times
func extractMinWeightAndAdjust(MinHeapSet []MinHeap) int {

	// Create Min Heap
	// CurrentSize/2 -1 are all the non-leaf nodes
	// Start with lowest level of non-leaf nodes and their children
	// Move smaller values up, push larger values down

	for i := CurrentSize/2 - 1; i >= 0; i-- {
		createMinHeapNodeWeight(MinHeapSet, i)
	}

	// Min value is at root (list[0])
	// All roots now less than its children, but not yet sorted

	// Debug
	//printMinHeap(list)

	// swap last element (list[CurrentSize-1] and root (list[0])
	min := MinHeapSet[0].value
	mini := MinHeapSet[0].Idx
	if CurrentSize > 0 {
		MinHeapSet[0].value = MinHeapSet[CurrentSize-1].value
		MinHeapSet[0].Idx = MinHeapSet[CurrentSize-1].Idx
		MinHeapSet[CurrentSize-1].value = min
		MinHeapSet[CurrentSize-1].Idx = mini

		// Reduce size by one as one Min value has been extracted (Min value is at the end of the list now)
		CurrentSize--
	}
	return mini
}

func calcShortestPathWeight(gr *Graph, root int, j int) int {

	// id of the edge
	eid := gr.nodes[root].aedges[j]
	// Destination id or index of the edge
	dst := gr.edges[eid].dst
	// src node weight + edge weight
	p := gr.nodes[root].params + gr.edges[eid].params
	// min (src node weight + edge weight, dst node weight)
	// 1st min weight path
	if p < gr.nodes[dst].params {
		gr.nodes[dst].params = p
		// Arrived to dst via eid
		gr.nodes[dst].sptedge[0] = eid
		// To keep track of ECMP paths
		gr.nodes[dst].lpr = true
		gr.nodes[dst].nsptedge = 1
		gr.edges[eid].spt = true
	} else {
		// 2nd min weight ECMP path
		// Multiple edges may lead to node with lower or same weight
		// = for keeping track of ECMP paths
		// For example: 10, 10, then 8, 8, 8
		// Arrive to dst node with params 10 via edge 1, Parms 10 via edge 3
		// Params 8, via other 3 edges --> we need to replace
		// First sptedge[0] gets replaced in above if block
		// Then if = && lpr=true, replace existing eids else append new ECMP paths
		if p == gr.nodes[dst].params {
			//var eid2 int
			if gr.nodes[dst].lpr { // if lower weight found above, then replace
				// ECMP path kept track of in destination node(s)
				gr.nodes[dst].sptedge[1] = eid
				gr.nodes[dst].nsptedge = 2
				gr.edges[eid].spt = true
				gr.nodes[dst].lpr = false
				// 3rd to n min weight ECMP path
			} else {
				n := gr.nodes[dst].nsptedge
				gr.nodes[dst].sptedge[n] = eid
				gr.nodes[dst].nsptedge++
				gr.nodes[dst].lpr = false
				gr.edges[eid].spt = true
			}
		}
	}
	return dst
}

// Traverses all the edges attached to a node
// For example: 0 16 5 & 0 16 2 4 5 & 0 1 3 7 8 2 4 5
// With Min Heap it should traverse only the Min path
func calcShortestPathTreeMinHeap(MinHeapSet []MinHeap, gr *Graph, root int) {

	if !gr.nodes[root].visited {
		gr.nodes[root].visited = true
		for j := range gr.nodes[root].aedges {
			dst := calcShortestPathWeight(gr, root, j)
			// Destination nodes are added to Min Heap
			// Do not add the dst node to Heap, if it has been added via another path
			if !gr.nodes[dst].addedMH {
				// Add dst to MinHeapSet
				gr.nodes[dst].addedMH = true
				MinHeapSet[CurrentSize].Idx = dst
				MinHeapSet[CurrentSize].value = gr.nodes[dst].params
				CurrentSize++
			}
		}
	}
}

// sr: source node index
// Create Min Weight Graph rooted at sr
func createMinWeightGraph(gr *Graph, sr int) {

	gr.nodes[sr].params = 0
	gr.nodes[sr].sptedge[0] = 0

	MinHeapSet := initMinHeap(sr)

	for range gr.nodes {
		mini := extractMinWeightAndAdjust(MinHeapSet)
		calcShortestPathTreeMinHeap(MinHeapSet, gr, mini)
	}
}

// Find Source sr to Destination dt shortest path with ECMP and store path in stack
// It also fills in with Next hop node name in NHop2Leaves
func pathSrc2Dst(gr *Graph, stackp *Stacki, sr, dt int, source int, lf string) {

	if dt != sr {

		// eid of shortest path edge leading to destination
		for j := 0; j < gr.nodes[dt].nsptedge; j++ {
			stackp.Push(dt)

			eid := gr.nodes[dt].sptedge[j]
			// source of that shortest path edge
			src := gr.edges[eid].src

			if src == source {
				nh := NHop2Leaves[lf]
				// nh should not be nil as it has been created before when node was added
				if nh != nil {
					ip := gr.nodes[dt].nm
					pr := gr.edges[eid].params

					// first var is either ip or " " and ne is bool
					_, ne := nh[ip] // There can be duplicates of Next hop --> ignore duplicates
					// like .4-->.5-->.13, .4-->.55-->.13: in both cases nexthop for .13 is .4

					if !ne {
						nh[ip] = pr
					}
				}
			}
			pathSrc2Dst(gr, stackp, sr, src, source, lf)
		}
	} else {
		stackp.Push(sr)
	}
}

/**************************************************************************************
	Min Weight Topology computation related print functions in GraphViz DOT format
***************************************************************************************/

// Print Min Weight Graph
// sr: source node index
func printMinWeightGraphDOT(gr *Graph, sr int) string {

	var line string

	//line = fmt.Sprintf("digraph {\n layout=\"circo\";\n")
	line = fmt.Sprintf("digraph {\n")

	line += fmt.Sprintf("\"%s\"[label=\"%s\n%s\n%d\", color=red, shape=oval]\n", gr.nodes[sr].nm, gr.nodes[sr].nm, gr.nodes[sr].ip, gr.nodes[sr].params)
	// Prints in Graphviz DOT notation
	for i := 0; i < NUMNODES; i++ {
		ip := gr.nodes[i].ip
		nm := gr.nodes[i].nm
		//_, t := Leaves[ip]
		_, t := Leaves[nm]
		if t { // It is a leaf
			line += fmt.Sprintf("\"%s\"[label=\"%s\n%s\n%d\", shape=\"rectangle\"];\n", nm, nm, ip, gr.nodes[i].params)
		} else {
			line += fmt.Sprintf("\"%s\"[label=\"%s\n%s\n%d\", shape=\"oval\"];\n", nm, nm, ip, gr.nodes[i].params)
		}
		for j := range gr.nodes[i].aedges {
			eid := gr.nodes[i].aedges[j]
			dstip := gr.edges[eid].dstip
			dstnm := gr.edges[eid].dstnm
			dst := gr.edges[eid].dst
			_, t := Leaves[dstnm]
			if t { // It is a leaf
				line += fmt.Sprintf("\"%s\"[label=\"%s\n%s\n%d\", shape=\"rectangle\"];\n", dstnm, dstnm, dstip, gr.nodes[dst].params)
			} else {
				line += fmt.Sprintf("\"%s\"[label=\"%s\n%s\n%d\", shape=\"oval\"];\n", dstnm, dstnm, dstip, gr.nodes[dst].params)
			}
			line += fmt.Sprintf("\"%s\" -> \"%s\"[label=\"%d\", weight=\"%d\"];\n", gr.nodes[i].nm, dstnm, gr.edges[eid].params, gr.edges[eid].params)
		}
	}
	line += fmt.Sprintf("}\n")

	return line
}

// Print Shortest path Tree with ECMP
// Min weight graph with given source has to be created first
//func printSPTECMPfile(gr *Graph) {
func printSPTECMPDOT(gr *Graph) string {

	var line string

	line = fmt.Sprintf("digraph {\n")

	// Prints in Graphviz DOT notation
	for i := 0; i < NUMNODES; i++ {

		ip := gr.nodes[i].ip
		nm := gr.nodes[i].nm
		_, t := Leaves[nm]
		if t { // It is a leaf
			line += fmt.Sprintf("\"%s\"[label=\"%s\n%s\n%d\", shape=\"rectangle\"];\n", nm, nm, ip, gr.nodes[i].params)
		} else {
			line += fmt.Sprintf("\"%s\"[label=\"%s\n%s\n%d\", shape=\"oval\"];\n", nm, nm, ip, gr.nodes[i].params)
		}

		for j := 0; j < gr.nodes[i].nsptedge; j++ {
			eid := gr.nodes[i].sptedge[j]
			line += fmt.Sprintf("\"%s\" -> \"%s\"[label=\"%d\", weight=\"%d\"];\n", gr.edges[eid].srcnm, gr.nodes[i].nm, gr.edges[eid].params, gr.edges[eid].params)
		}
	}
	line += fmt.Sprintf("}\n")

	return line

}

// Print in DOT format source to destination shortest path with ECMP
func printSPECMPDOT(gr *Graph, stackp *Stacki, dest int) string {

	var line string

	line = fmt.Sprintf("digraph {\n")

	// stackp.count keeps dcreasing at each pop
	for stackp.count > 0 {
		v := stackp.Pop()
		if v == dest {
			line += fmt.Sprintf("\"%s\";\n", gr.nodes[v].ip)
		} else {
			line += fmt.Sprintf("\"%s\" -> ", gr.nodes[v].ip)
		}
	}
	line += fmt.Sprintf("}\n")
	return line
}

/**************************************************************************************
	Topology update related functions
***************************************************************************************/

func AddNode(rq TopoNode) error {

	var ni Topology

	tn := rq.Name

	_, ok := NodeToID[tn]
	if !ok {
		NodeToID[tn] = rq.ID
	}

	vl := InitialTopology[tn]
	if vl == nil { // first time being added or added after deletion

		//ni = new(Topology)
		ni = Topology{}
		//ni.ThisNode.ID = tn
		ni.ThisNode.Name = rq.Name
		ni.ThisNode.ID = rq.ID
		ni.ThisNode.Idx = IDX

		ni.ThisNode.MicroVNF = rq.MicroVNF
		InitialTopology[tn] = &ni

		// This node may not have been active before, but was added as neighbor
		// by another node before it was active / launched
		pn := PendingNB[tn]
		if pn != nil {
			for i := range pn {
				nn := pn[i].ThisNodeName
				nb := InitialTopology[nn]
				if nb != nil {
					nb.Neighbors = append(nb.Neighbors, pn[i])
				}
			}
		}

		// Create separate map for non-Micro-VNF (Leaf) nodes with Next hops toward the leaf node
		// Next hop will be filled in when request comes in for it via GetNextHopsToLeaves
		//if !ni.ThisNode.MicroVNF {
		if !rq.MicroVNF {
			lf := NHop2Leaves[tn]
			if lf == nil { // A leaf may be reachable from multiple paths
				nh := make(map[string]int)
				NHop2Leaves[tn] = nh
				Leaves[tn] = IDX
			}
		}
		IDX++
		fmt.Printf("Node %s added\n", tn)
		return nil
	}
	// Future: add update of node
	//fmt.Printf("MinWeighTopologyService:AddNode: Node %s Exists\n", tn)
	return nil
}

func DeleteNode(rq TopoNode) error {

	tn := rq.Name
	vl := InitialTopology[tn]
	if vl != nil {
		for i := range vl.Neighbors {
			nn := InitialTopology[vl.Neighbors[i].NeighborName]
			if nn != nil {
				//  Go to the  neighbors and delete this node from neighbors
				n1 := nn.Neighbors
				for j := range n1 {
					if n1[j].NeighborName == tn {
						nb := deleteNeighbor2(n1, j)
						nn.Neighbors = nb
					}
				}
				// If this node is leaf, delete it, if it has no neighbors
				// If a MVNF has no neighbors, it is not deleted (may be should)
				// # of neighbors of neighbor of this node (tn)
				v2 := InitialTopology[vl.Neighbors[i].NeighborName]
				var l int
				if v2 != nil {
					l = len(v2.Neighbors)
				}
				if !vl.Neighbors[i].MicroVNF && l == 0 {
					delete(InitialTopology, vl.Neighbors[i].NeighborName)
					delete(NHop2Leaves, vl.Neighbors[i].NeighborName)
					delete(Leaves, vl.Neighbors[i].NeighborName)
					delete(PendingNB, vl.Neighbors[i].NeighborName)
					DeleteList[vl.Neighbors[i].NeighborName] = true
				}
			}
		}
		// Delete this node
		delete(InitialTopology, tn)
		DeleteList[tn] = true

		// Idx should be updated for InitGraph
		IDX = 0
		for k, v := range InitialTopology {
			v.ThisNode.Idx = IDX
			_, n := Leaves[k]
			if n {
				Leaves[k] = IDX
			}

			IDX++
		}
		fmt.Printf("Node %s deleted\n", tn)
		return nil
	}
	//return fmt.Errorf("MinWeighTopologyService:DeleteNode: Node %s does not exist", tn)
	return fmt.Errorf("Node %s does not exist", tn)

}

// Add neighbor to ThisNode
func AddNeighbor(ni TopoNeighbor) error {

	tn := ni.ThisNodeName

	// vl: Pointer to Topology
	vl := InitialTopology[tn]
	if vl == nil { // Node has to exist already
		return fmt.Errorf("TopoProcessor: Add Neighbor: Node %s must exist before Neighbor %s addition", tn, ni.NeighborName)
	}
	for i := range vl.Neighbors {
		if vl.Neighbors[i].NeighborName == ni.NeighborName {
			// This should be supported in future and there can be multiple interfaces between pair of MVNF
			// Or call UpdateNeighbor
			return fmt.Errorf("TopoProcessor: Add Neighbor: Attempt to add an Existing Neighbor %s", ni.NeighborName)
		}
	}
	// Neighbor node must exist also - MVNF may not have been started yet
	nn := InitialTopology[ni.NeighborName]
	if nn != nil { // Neighbor node exists
		vl.Neighbors = append(vl.Neighbors, ni)
	} else {
		// Place it in pending list of neighbors to be added when MVNF ni.NeighborID comes up
		PendingNB[ni.NeighborName] = append(PendingNB[ni.NeighborName], ni)
		return fmt.Errorf("TopoPRocessor: Add Neighbor: Micro-VNF Neighbor %s for %s does not exist yet", ni.NeighborName, tn)
	}

	return nil
}

func DeleteNeighbor(ni TopoNeighbor) error {

	tn := ni.ThisNodeName
	// vl: Pointer to Topology
	vl := InitialTopology[tn]
	if vl == nil { // Node has to exist already
		return fmt.Errorf("TopoProcessor: Delete Neighbor: Node %s must exist before Neighbor %s deletion", tn, ni.NeighborName)
	}

	// linear search can be replaced with faster search like heap sort/search, if number of edges are really large
	for i := range vl.Neighbors {
		if vl.Neighbors[i].NeighborName == ni.NeighborName {
			nb := deleteNeighbor2(vl.Neighbors, i)
			vl.Neighbors = nb
			break
		}
	}
	return nil
}

func UpdateNeighbor(ni TopoNeighbor) error {

	tn := ni.ThisNodeName
	// vl: Pointer to Topology
	vl := InitialTopology[tn]
	if vl == nil { // Node has to exist already
		return fmt.Errorf("TopoProcessor: Update Neighbor: Node %s must exist before Neighbor %s update", tn, ni.NeighborName)
	}
	// linear search can be replaced with faster search like heap sort/search, if number of edges are really large
	for i := range vl.Neighbors {
		if vl.Neighbors[i].NeighborName == ni.NeighborName {
			// update weight & status
			vl.Neighbors[i].EdgeWeight = ni.EdgeWeight
			break
		}
	}
	return nil
}

/**************************************************************************************
	Service related  functions calling RPC functions (should go in shared folder)
***************************************************************************************/

func GetAllServiceInfoFromExistingGK(sr, pr, ts string) error {

	// To Add: retry
	c, err := rpc.Dial("tcp", sr+":"+pr)
	if err != nil {
		return err
	}
	// Arg is ALL; returns ServiceMap
	err = c.Call("ServiceMapper.GetAllServiceInfo", ts, &ServiceMap)

	if err != nil {
		return err
	}
	//PrettyPrintJSON(r, "INIT Service Info")
	return nil
}

func SendInitTopoRequest(sr, pr string) error {

	// To Add: retry
	c, err := rpc.Dial("tcp", sr+":"+pr)
	if err != nil {
		return err
	}
	// Arg is ALL; returns ServiceMap
	err = c.Call("TopoProcessor.GetInitialTopology", ThisNodeIP, &TopoStates)

	if err != nil {
		return err
	}
	//PrettyPrintJSON(r, "INIT Service Info")
	return nil
}

// A newly launched MWT is initialized from existing MWT
func GetInitTopoFromMWT() {

	pts := TopoStates
	// Get from MWT having highest ServiceKnowledge
	v := ServiceMap["TopoProcessor"]
	if v != nil {
		for i := range v {
			if v[i].ServiceStatus == 2 && v[i].ServiceIP != ThisNodeIP { // Service is up
				SendInitTopoRequest(v[i].ServiceIP, v[i].ServicePort)
				if len(TopoStates.InitialTopology) > len(pts.InitialTopology) {
					pts = TopoStates
				}
			}
		}
		InitialTopology = pts.InitialTopology
		PendingNB = pts.PendingNB
		NHop2Leaves = pts.NHop2Leaves
		Leaves = pts.Leaves
		IDX = pts.IDX

		PrintInitialTopology()
	}
}

// This GK service registered to other GK services
// GK service host, port info, this service info
func RegisterThisService(h, p string, ts *ServiceInfo) {

	c, err := rpc.Dial("tcp", h+":"+p)
	if err != nil {
		fmt.Println(err)
		return
	}

	var result ServiceInfo

	err = c.Call("ServiceMapper.RegisterService", ts, &result)
	if err != nil {
		fmt.Println(err)
	} else {
		//fmt.Println("Response from GateKeeper:\n", result)
		PrettyPrintJSON(result, "RegisterThisService: Response from ServiceMapper")

	}
}

// NOT USED HERE
// Register services
func UpdateServiceInfo(s ServiceInfo) {

	// A service is running on multiple servers and ports

	//sn := []string{}
	n := s.ServiceName
	// vl1 is ServerInfo
	vl1 := ServiceMap[n]
	if vl1 == nil { // first element in the map
		ServiceMap[n] = append(ServiceMap[n], s)
	} else {
		found := false
		// Same server may be registering again, can be also with different port # & other info
		// Find it in the list and update
		// ****** If server is localhost following should be commented out  ******

		for n := range vl1 {
			if vl1[n].ServiceIP == s.ServiceIP {
				// update port
				vl1[n].ServicePort = s.ServicePort
				vl1[n].ServiceStatus = 2
				vl1[n].ServiceKnowledge = 0
				vl1[n].NetNodeID = ThisNodeIP
				vl1[n].ServiceLaunchTime = LocalTimeMs()
				vl1[n].ServiceUpdateTime = LocalTimeMs()
				found = true
				break
			}
		}

		// This is a new server for the same service name
		if !found {
			ServiceMap[n] = append(ServiceMap[n], s)
		}
	}
	//PrettyPrintJSON(s, "UpdateServiceInfo: Registered")
	fmt.Printf("%s %s:%s Registered\n", n, s.ServiceIP, s.ServicePort)

}

// Every configured interval get all the service info
func GetActiveServiceInfo(i time.Duration) {

	//tick := time.NewTicker(PingInt)
	tick := time.NewTicker(i)

	for {
		select {
		case <-tick.C:
			v := ServiceMap["ServiceMapper"]
			for i := range v {
				if v[i].ServiceStatus == 2 { // Service is up
					e := GetAllServiceInfoFromExistingGK(v[i].ServiceIP, v[i].ServicePort, ThisNodeIP)
					if e != nil {
						fmt.Println(e)
					} else {
						break // Add: Get from service having most info
					}
				}
			}
		}
	}
}

/**************************************************************************************
	Launch this service
***************************************************************************************/

// RPC over TCP (other over HTTP, JSON RPC)
func LaunchService(s, p string) {

	rpc.Register(new(TopoProcessor))

	t, err := net.Listen("tcp", s+":"+p)
	if err != nil {
		fmt.Println(err)
		return
	}
	for {
		c, err := t.Accept()
		if err != nil {
			continue
		}
		go rpc.ServeConn(c)
	}
}

/**************************************************************************************
   RPC Functions for TopoProcessor that are called by outside "clients"
***************************************************************************************/

// Not used
func (s *TopoProcessor) Liveness(req int, reply *string) error {

	*reply = LocalTimeMs()
	return nil
}

func (s *TopoProcessor) PingResponse(req int, reply *int) error {

	//*reply = len(InitialTopology)
	//r := []string{"TNodes", strconv.Itoa(NUMNODES), "TEdges", strconv.Itoa(NUMEDGES)}
	*reply = NUMNODES + NUMEDGES
	return nil
}

// req IP address
// Min weight graph (topology) rooted at source (v.Idx) in DOT notation is returned
func (s *TopoProcessor) GetMinWeightTopologyinDOT(req string, reply *string) error {

	fmt.Printf("%s requests Min Weight Topology in DOT\n", req)

	// Graph has to initilized every time as each request may have different source or root
	// Min weight graph is different for different source
	// Min Weight Graph can be cached (***** ADD CACHING LATER *****)
	gr := initGraph()
	if gr == nil {
		return errors.New("TopoProcessor: Graph size 0 or 2 nodes with no edges")
	}
	v := InitialTopology[req]
	if v != nil {
		//fmt.Printf("GetMinWeightTopology IP Idx %s %d REQ %s\n", v.ThisNode.ID, v.ThisNode.Idx, req)
		createMinWeightGraph(gr, v.ThisNode.Idx)
		dt := printMinWeightGraphDOT(gr, v.ThisNode.Idx)
		*reply = dt
		return nil
	}
	return fmt.Errorf("Node %s does not exist", req)
}

// Shortest Path Tree (SPT) with ECMP in DOT notation
func (s *TopoProcessor) GetECMPSPTinDOT(req string, reply *string) error {

	fmt.Printf("%s requests SPT with ECMP\n", req)

	// Graph has to be initilized every time as each request may have different source or root
	// Min weight graph is different for different source
	// Min Weight Graph for a source can be cached (***** ADD CACHING LATER *****)
	gr := initGraph()
	if gr == nil {
		return errors.New("TopoProcessor: Graph size 0 or 2 nodes with no edges")

	}
	v := InitialTopology[req]
	if v != nil {
		createMinWeightGraph(gr, v.ThisNode.Idx)
		dt := printSPTECMPDOT(gr)
		*reply = dt
		return nil
	}
	return fmt.Errorf("TopoProcessor:GetECMPSPTinDOT: Node %s does not exist", req)
}

//  source to destination Shortest Path with ECMP in DOT notation
func (s *TopoProcessor) GetECMPSPSrcToDstInDOT(req PathRequest, reply *string) error {

	fmt.Printf("Get path for source %s - destination %s", req.src, req.dst)

	// Graph has to be initilized every time as each request may have different source or root
	// Min weight graph is different for different source
	// Min Weight Graph for a source can be cached (***** ADD CACHING LATER *****)
	gr := initGraph()
	if gr == nil {
		return errors.New("TopoProcessor.GetECMPSPSrcToDstInDOT: Graph size 0 or 2 nodes with no edges")
	}
	// Need to add check on InitialTopology (check on len == 0)
	v := InitialTopology[req.src]
	d := InitialTopology[req.dst]
	if v != nil && d != nil {
		createMinWeightGraph(gr, v.ThisNode.Idx)
		// path stored in stack
		stackp := &Stacki{value: make([]int, NUMEDGES*10)}
		pathSrc2Dst(gr, stackp, v.ThisNode.Idx, d.ThisNode.Idx, v.ThisNode.Idx, req.dst)
		// path popped from stack and printed
		dt := printSPECMPDOT(gr, stackp, d.ThisNode.Idx)
		*reply = dt
		return nil
	}
	return fmt.Errorf("TopoProcessor:GetECMPSPSrcToDstInDOT: source %s - destination %s does not exist", req.src, req.dst)

}

// Get Next Hops from source to leaf (non-Micro-VNF) nodes on shortest ECMP path
func (s *TopoProcessor) GetNextHopsToLeaves(req string, reply *map[string]map[string]int) error {

	fmt.Printf("%s requests Next Hop to Leaves\n", req)
	// ADD: Need to clear from NHop2Leaves previous next hops calculated for another source

	gr := initGraph()
	if gr == nil {
		return errors.New("TopoProcessor.GetNextHopsToLeaves: Graph size 0 or 2 nodes with no edges")
	}
	// Need to add check on InitialTopology (check on len == 0)
	v := InitialTopology[req]
	if v != nil {
		createMinWeightGraph(gr, v.ThisNode.Idx)
		// path stored in stack: not quite needed for this
		// Multiple of 5 - WHAT IF NODE SIZE INCREASES beyond this #
		// (Stacki dynamic allocation does not seem to work)
		// Stack depth should be NUMEDGES+1?
		//stackp := &Stacki{value: make([]int, NUMNODES*5)}
		stackp := &Stacki{value: make([]int, NUMEDGES*10)}
		// Fill in with next hop info
		// From each leaf trace back to source to fill in next hop from source
		// Can possibly be done in other ways - this is nl*logn (nl: # of leaves; n: total # of nodes)
		for k := range NHop2Leaves {
			// clean out next hops from previous call
			NHop2Leaves[k] = nil
			NHop2Leaves[k] = make(map[string]int)
			l := Leaves[k]
			pathSrc2Dst(gr, stackp, v.ThisNode.Idx, l, v.ThisNode.Idx, k)
		}

		// pathSrc2Dst places leaf node itself as next hop when the leaf is attached to the req node
		// Next hop should be 0.0.0.0 as leaf is directly attached

		for k, v := range NHop2Leaves {
			// Next hop same as leaf?
			_, m := v[k]
			if m {
				w := v[k]
				delete(v, k)
				v[req] = w
			}
		}

		for k, v := range NHop2Leaves {
			i1 := NodeToID[k]
			nh := make(map[string]int)
			for k1, v1 := range v {
				i2 := NodeToID[k1]
				nh[i2] = v1
			}
			NHop2LeavesID[i1] = nh
		}

		fmt.Println()

		*reply = NHop2LeavesID

		// stackp can be global
		stackp = nil

		return nil
	}
	return fmt.Errorf("TopoProcessor.GetNextHopsToLeaves: Node %s does not exist", req)
}

func (s *TopoProcessor) AddNodeInTopology(req TopoNode, reply *int) error {

	fmt.Printf("TopoProcessor: Add Node %s %s\n", req.Name, req.ID)

	e := AddNode(req)
	*reply = len(InitialTopology)
	return e
}

func (s *TopoProcessor) DeleteNodeInTopology(req TopoNode, reply *int) error {

	fmt.Printf("TopoProcessor: Delete Node %s\n", req.ID)

	e := DeleteNode(req)
	*reply = len(InitialTopology)
	return e
}

func (s *TopoProcessor) AddNeighborInTopology(req TopoNeighbor, reply *int) error {

	//fmt.Printf("Add Neighbor %s for %s\n", req.NeighborID, req.ThisNodeID)
	fmt.Printf("TopoProcessor: Add Neighbor %s for %s\n", req.NeighborName, req.ThisNodeName)

	e := AddNeighbor(req)
	*reply = len(InitialTopology)
	return e
}

func (s *TopoProcessor) DeleteNeighborInTopology(req TopoNeighbor, reply *int) error {

	fmt.Printf("TopoProcessor: Delete Neighbor %s from %s\n", req.NeighborName, req.ThisNodeName)

	e := DeleteNeighbor(req)
	*reply = len(InitialTopology)
	return e
}

func (s *TopoProcessor) UpdateNeighborInTopology(req TopoNeighbor, reply *int) error {

	fmt.Printf("TopoProcessor: Update Neighbor %s for %s\n", req.NeighborName, req.ThisNodeName)

	e := UpdateNeighbor(req)
	*reply = len(InitialTopology)
	return e
}

// Given a node info return Node and Neighbor (Topology) information
func (s *TopoProcessor) GetNodeInfo(req string, reply *Topology) error {

	fmt.Printf("TopoProcessor: %s requests Node info", req)

	n := InitialTopology[req]
	*reply = *n
	return nil
}

// Newly launched MWT gets InitialTopology, NHop2Leaves and PendingNB from active MWT
func (s *TopoProcessor) GetInitialTopology(req string, reply *TopologyStates) error {

	fmt.Printf("TopoProcessor: %s requests Topology States\n", req)

	ts := TopologyStates{}
	ts.IDX = IDX
	ts.InitialTopology = InitialTopology
	ts.NHop2Leaves = NHop2Leaves
	ts.PendingNB = PendingNB
	ts.Leaves = Leaves
	*reply = ts
	return nil
}

// reply string (add JSON later)
// req: requester node IP
func (s *TopoProcessor) GetInitTopologyInDOT(req string, reply *string) error {

	fmt.Printf("%s requests Initial Topology in DOT\n", req)
	var str string
	//str = fmt.Sprintf("digraph {\n layout=\"circo\";\n")
	str = fmt.Sprintf("digraph {\n")

	for i := range InitialTopology {
		j := InitialTopology[i]
		t := j.ThisNode.ID
		o := j.ThisNode.Name
		if !j.ThisNode.MicroVNF {
			str += fmt.Sprintf("\"%s\"[label=\"%s\n%s\", shape=\"rectangle\"];\n", o, o, t)
		} else {
			str += fmt.Sprintf("\"%s\"[label=\"%s\n%s\", shape=\"oval\"];\n", o, o, t)
		}
		n := j.Neighbors
		l := len(n)
		for k := 0; k < l; k++ {
			e := n[k].NeighborName
			w := n[k].EdgeWeight
			str += fmt.Sprintf("\"%s\" -> \"%s\"[label=\"%d\", weight=\"%d\"];\n", o, e, w, w)
		}
	}
	str += fmt.Sprintf("\n}\n")
	*reply = str
	return nil
}

// When topology updated, TopologyService pushes InitialTopology
// Other option to pull InitialTopology when clients calls
func (s *TopoProcessor) RefreshInitialTopology(req int, reply *int) error {

	*reply = len(InitialTopology)
	return nil
}

func getServiceInfoAndRegister(ts ServiceInfo) {

	gi := []string{}
	rp := ts.Replica
	nm := ts.ServiceMapper
	ns := ts.NameSpace
	cd := ts.ClusterDomain
	gp := ts.ServiceMapperPort

	//time.Sleep(time.Second * 180)

	//for k := 0; k < 5; k++ {

	for i := 0; i < rp; i++ {
		//hh := nm + "-" + strconv.Itoa(i) + "." + nm + "." + ns + ".svc.cluster.local"
		hh := nm + "-" + strconv.Itoa(i) + "." + nm + "." + ns + "." + cd
		fmt.Println(hh)

		gi = append(gi, hh)
	}

	for j := range gi {
		e := GetAllServiceInfoFromExistingGK(gi[j], gp, ThisNodeIP)
		// Get from one; Later ADD: Get from one having most info
		// That is ServiceKnowledge highest
		if e == nil {
			break
		} else {
			fmt.Println(e)
		}
	}

	if ServiceMap != nil {
		v := ServiceMap["ServiceMapper"]
		if v != nil {
			for i := range v {
				//if v[i].ServiceMeta.(int) >= 0 { // server not down
				//if v[i].ServiceStatus == 2 { // Service is up
				fmt.Printf("Registering %s %s with %s %s\n", ThisNodeName, ts.ServiceIP, v[i].ServiceInstance, v[i].ServiceIP)
				RegisterThisService(v[i].ServiceIP, v[i].ServicePort, &ts)
				//}
			}
		}
	}
}

func getServiceInfoAndRegister1(ts ServiceInfo) {

	gi := []string{}
	rp := ts.Replica
	nm := ts.ServiceMapper
	ns := ts.NameSpace
	cd := ts.ClusterDomain
	gp := ts.ServiceMapperPort

	for i := 0; i < rp; i++ {
		hh := nm + "-" + strconv.Itoa(i) + "." + nm + "." + ns + "." + cd

		fmt.Println(hh)

		gi = append(gi, hh)
	}

	for j := range gi {
		e := GetAllServiceInfoFromExistingGK(gi[j], gp, ThisNodeIP)
		// Get from one; Later ADD: Get from one having most info
		// That is ServiceKnowledge highest
		if e == nil {
			break
		} else {
			fmt.Println(e)
		}
	}

	if ServiceMap != nil {
		v := ServiceMap["ServiceMapper"]
		if v != nil {
			for i := range v {
				//if v[i].ServiceStatus == 2 { // Service Mapper is up
				fmt.Printf("Registering %s %s with %s %s\n", ThisNodeName, ts.ServiceIP, v[i].ServiceInstance, v[i].ServiceIP)
				RegisterThisService(v[i].ServiceIP, v[i].ServicePort, &ts)
				//}
			}
		}
	}

	GetInitTopoFromMWT()
}

func main() {

	var e error
	IDX = 0

	//gi := []string{}

	InitialTopology = make(map[string]*Topology)
	PrevInitialTopology = make(map[string]*Topology)
	NHop2Leaves = make(map[string]map[string]int)
	NHop2LeavesID = make(map[string]map[string]int)
	Leaves = make(map[string]int)
	ServiceMap = make(map[string][]ServiceInfo)
	PendingNB = make(map[string][]TopoNeighbor)
	TopoStates = TopologyStates{}
	DeleteList = make(map[string]bool)
	// Should map to multiple ID struct IPv4, IPv6, MAC
	NodeToID = make(map[string]string)

	ts := ReadJSONInfo("./Configs/MWTConfig.json", "MWT Service Info")

	nm := ts.ServiceName
	ns := ts.NameSpace
	cd := ts.ClusterDomain
	hn := os.Getenv("HOSTNAME") + "." + nm + "." + ns + "." + cd
	//hn := os.Getenv("HOSTNAME") + ".gks.default.svc.cluster.local"
	fmt.Println(hn)

	hip, e := GetIPv4()
	if e != nil {
		fmt.Println(e)
		os.Exit(1)
	}
	//fmt.Printf("Service Mapper's IP %s\n", hip)
	ThisNodeIP = hip
	ThisNodeName = os.Getenv("HOSTNAME")
	ts.ServiceIP = ThisNodeIP
	ts.ServiceInstance = hn
	ts.ServiceRPCName = "TopoProcessor"

	//go getServiceInfoAndRegister(ts)
	getServiceInfoAndRegister(ts)

	fmt.Printf("Launching Min Weight Topo Computation Service %s %s %s\n", ThisNodeName, ts.ServiceIP, ts.ServicePort)
	LaunchService(hn, ts.ServicePort)

}
