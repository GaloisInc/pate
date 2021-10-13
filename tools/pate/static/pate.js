/**
  * Construct an ID for the HTML element containing the text of a basic block node
  */
function labelContainerID(data, variant) {
    return 'pre-' + variant + '-' + data.id;
}

/**
  * Scroll the selected node body (the pre tag containing the text) if there is only one selected
  *
  * If this function scrolls the single selected node, it prevents the page from scrolling at the same time.
  */
function scrollSelectedGraphNodeLabel(cy, e, variant, amount) {
    var sel = cy.$(':selected');
    if(sel.length == 1) {
        var pre = document.getElementById(labelContainerID(sel[0].data(), variant));
        pre.scrollBy(0, amount);
        e.stopPropagation();
        e.preventDefault();
    }
}

var sliceGraphNodeStyle = { shape: 'round-rectangle',
                            width: '400px',
                            height: '500px',
                            events: 'yes',
                            'text-events': 'yes'
                          };
var sliceGraphConfig = { style: sliceGraphNodeStyle,
                         nodeClass: 'slice-graph-node-label',
                         nodeBackgroundColor: function(ele) { return 'gray'; },
                         nodeTapHandler: false
                       };

function proofNodeColor(nodeType) {
    switch(nodeType) {
    case 'Slice':
        return '#65c5eb';
    case 'Call':
        return 'orange';
    case 'Triple':
        return '#d4d9d5';
    case 'Triple(FunctionPredomain)':
        return '#d4d9d5';
    case 'Triple(SliceSummary)':
        return '#d4d9d5';
    case 'Triple(Unknown)':
        return 'red';
    case 'Status(Success)':
        return '#94d498';
    case 'Status(Inequivalent)':
        return 'red';
    case 'Status(Conditional)':
        return 'yellow';
    case 'Status(Skipped)':
        return 'white';
    case 'Status(Unverified)':
        return 'white';
    case 'Domain':
        return 'brown';
    }

    // Root color
    return 'pink';
}

function proofNodeTapHandler(cy, nodeClickCallback) {
    return function (evt) {
        if(!nodeClickCallback) return;
        if(evt.target === cy) return;

        nodeClickCallback(parseInt(evt.target.data("id"), 10));
    };
}

var proofGraphNodeStyle = { shape: 'round-rectangle',
                            width: '200px',
                            height: '50px',
                            'background-color': function(ele) { return proofNodeColor(ele.data('nodeType')); },
                            border: '2px dotted black',
                            events: 'yes',
                            'text-events': 'yes'
                          };
function proofGraphConfig() {
    return { style: proofGraphNodeStyle,
             nodeClass: 'proof-graph-node-label',
             nodeTapHandler: proofNodeTapHandler
           };
}

/**
 * Initialize a graph in the given div with the given data (which corresponds to a cytoscape elements map)
 *
 * @param{string} divId
 * @param{Object} graphData
 */
function initializeGraphIn(nodeClickCallback, divId, nodeConfig, graphData) {
    var cy = cytoscape({
        container: document.getElementById(divId),
        elements: graphData,
        style: [
            { selector: 'node',
              style: nodeConfig.style
            },
            { selector: 'edge',
              style: {
                  'width': 3,
                  'curve-style': 'taxi',
                  'line-color': '#ccc',
                  'target-arrow-color': '#ccc',
                  'target-arrow-shape': 'triangle'
              }
            }
        ]
    });

    if(nodeConfig.nodeTapHandler) {
        cy.on('tap', nodeConfig.nodeTapHandler(cy, nodeClickCallback));
    }

    cy.nodeHtmlLabel([{
        query: 'node',
        tpl: function(data) {
            return '<pre id="' + labelContainerID(data, divId) + '" class="' + nodeConfig.nodeClass + '">' + data.text + '</pre>';
        }
    }], {enablePointerEvents: true});

    cy.layout({ name: 'dagre'
              }).run();

    document.addEventListener('keydown', function(e) {
        if(e.key == 'ArrowDown') {
            scrollSelectedGraphNodeLabel(cy, e, divId, 20);
        } else if(e.key == 'ArrowUp') {
            scrollSelectedGraphNodeLabel(cy, e, divId, -20);
        }
    });
}

