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
                         nodeBackgroundColor: function(ele) { return 'gray'; }
                       };

function proofNodeColor(nodeType) {
    switch(nodeType) {
    case 'Slice':
        return 'blue';
    case 'Call':
        return 'orange';
    case 'Triple':
        return 'gray';
    case 'Status(Success)':
        return 'green';
    case 'Status(Fail)':
        return 'red';
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
var proofGraphNodeStyle = { shape: 'round-rectangle',
                            width: '200px',
                            height: '50px',
                            'background-color': function(ele) { return proofNodeColor(ele.data('nodeType')); },
                            border: '2px dotted black'
                          };
function proofGraphConfig() {
    return { style: proofGraphNodeStyle,
             nodeClass: 'proof-graph-node-label'
           };
}

/**
 * Initialize a graph in the given div with the given data (which corresponds to a cytoscape elements map)
 *
 * @param{string} divId
 * @param{Object} graphData
 */
function initializeGraphIn(divId, nodeConfig, graphData) {
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
                  'curve-style': 'bezier',
                  'line-color': '#ccc',
                  'target-arrow-color': '#ccc',
                  'target-arrow-shape': 'triangle'
              }
            }
        ]
    });


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

