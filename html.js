/* Getting knowdes into HTML */

protoknowde.toHTML=function()
{
  if (this.dterm_base)
    return fdjtSpan("dterm",this.dterm_base,
		    fdjtSpan("disambig",this.dterm_disambig));
  else {
    var dterm=this.dterm;
    var colonpos=dterm.indexOf(':');
    if ((colonpos>0) && (colonpos<(dterm.length-1))) {
      if (dterm[colonpos+1].search(/\w/)===0)
	return fdjtSpan("dterm",dterm.slice(0,colonpos),
			dterm.slice(colonpos));}
    return fdjtSpan("dterm",dterm);}
};

/* Making DTERM descriptions */

function knoRelVal(v)
{
  if (typeof v === "string")
    return fdjtSpan("term",v);
  else if (v instanceof KnowdeType) {
    var span=fdjtSpan("dterm",v.dterm);
    span.setAttribute("dterm",v.dterm);
    return span;}
  else return fdjtNodify("???");
}

function knoAppendRel(elt,relname,relcode,relvals)
{
  if (!(relvals)) relvals=elt.knowde[relname];
  if ((!(relvals)) || (relvals.length===0)) return;
  var field=
    fdjtSpan("field",
	     fdjtSpan("val",
		      fdjtWithTitle(fdjtSpan("relcode",relcode),relname),
		      knoRelVal(relvals[0])));
  fdjtAppend(elt,field);
  var i=1; while (i<relvals.length) {
    var val=relvals[i++];
    fdjtAppend(field," ",
	       fdjtSpan("val",
			fdjtWithTitle(fdjtSpan("relcode",relcode),relname),
			knoRelVal(val)));}
  return field;
}

/* DTerm tips */

var knowlet_richtips={};

function KnowdeRichTip(elt) {
  // fdjtTrace("KnowdeRichTip %o",elt);
  if (typeof elt === "string") {
    var knowde=knowlet.KnowdeProbe(elt);
    if (knowde)
      return KnowdeRichTip(knowde);
    else return false;}
  else if (elt instanceof KnowdeType) {
    var knowde=elt;
    var dterm=knowde.dterm;
    if (knowlet_richtips[dterm])
      return knowlet_richtips[dterm];
    var richtip=fdjtDiv("richtip",fdjtSpan("dterm",dterm)," ");
    knowlet_richtips[dterm]=richtip;
    richtip.dterm=dterm;
    richtip.knowde=knowde;
    /* Initialize the richtip elements */
    fdjtRichTip_init(richtip);
    knoAppendRel(richtip,"genls","^");
    /* Insert related concepts and synonyms */
    if (knowde.gloss) 
      fdjtAppend(richtip," ",fdjtSpan("gloss",knowde.gloss));
    return richtip;}
  else if ((elt instanceof Node) && (elt.getAttribute('dterm')))
    return KnowdeRichTip(elt.getAttribute('dterm'));
  else return false;
}

fdjt_richtip_classfns["dterm"]=KnowdeRichTip;

/* Getting Knowlets out of HTML */

var _knowletsHTML_done=false;

function KnowletLoad(elt)
{
  var text=fdjtAjaxGetText(elt.src);
  var knowdes=knowlet.handleEntries(text);
  fdjtLog("Parsed %d entries from %s",knowdes.length,elt.src);
  if (elt.text) {
    var more_knowdes=knowlet.handleEntries(elt.text);
    fdjtLog("Parsed %d more entries from %s",knowdes.length);}
}

function knoHTMLSetup(node)
{
  var doing_the_whole_thing=false;
  if ((!(node)) || (node_arg===document))
    if (_knowletsHTML_done) return;
    else {
      if (!(node)) {
	node=document;
	doing_the_whole_thing=true;}
      else if (node===document)
	doing_the_whole_thing=true;}
  var elts=fdjtGetChildrenByTagName(document,"META");
  var i=0; while (i<elts.length) {
    var elt=elts[i++];
    if (elt.name==="KNOWLET") {
      knowlet=Knowlet(elt.content);}}
  if ((!(knowlet)) &&
      (document) && (document.location) &&
      (document.location.href)) {
    var url=document.location.href;
    var hash=url.indexOf("#");
    if (hash>=0) url=url.slice(0,hash);
    fdjtLog("Using '%s' as the name of the default knowlet",url);
    knowlet=Knowlet(url);}
  i=0; while (i<elts.length) {
    var elt=elts[i++];
    if (elt.name==="KNOWDEF") knowlet.handleEntry(elt.content);}
  elts=fdjtGetChildrenByTagName(document,"LINK");
  i=0; while (i<elts.length) {
    var elt=elts[i++];
    if (elt.name==="KNOWLET") {
      knowlet.handleEntry(elt.content);}}
  elts=fdjtGetChildrenByTagName(document,"SCRIPT");
  i=0; while (i<elts.length) {
    var elt=elts[i++];
    if ((elt.getAttribute("language")) &&
	((elt.getAttribute("language"))==="knowlet")) {
      if (elt.src) KnowletLoad(elt);
      else if (elt.text) {
	var knowdes=knowlet.handleEntries(elt.text);
	fdjtLog("Parsed %d entries from %o",knowdes.length,elt);}
      else {}}}
  if (doing_the_whole_thing) _knowletsHTML_done=true;
}
