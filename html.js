/* -*- Mode: Javascript; -*- */

/* Copyright (C) 2009-2010 beingmeta, inc.
   This file provides for HTML documents using KNOWLETS, including
    the extraction and processing of embedded KNOWLET definitions
    or references and interaction with interactive parts of the
    FDJT library.

   For more information on knowlets, visit www.knowlets.net
   This library is built on the FDJT (www.fdjt.org) toolkit.

   This program comes with absolutely NO WARRANTY, including implied
   warranties of merchantability or fitness for any particular
   purpose.

    Use, modification and redistribution of this program is permitted
    under the GNU General Public License (GPL) Version 2:

          http://www.gnu.org/licenses/old-licenses/gpl-2.0.html

    Use and redistribution (especially embedding in other
      CC licensed content) is permitted under the terms of the
      Creative Commons "Attribution-NonCommercial" license:

          http://creativecommons.org/licenses/by-nc/3.0/ 

    Other uses may be allowed based on prior agreement with
      beingmeta, inc.  Inquiries can be addressed to:

       licensing@biz.beingmeta.com

   Enjoy!

*/

var knowlets_trace_load=0;

/* Getting knowdes into HTML */

protoknowde.toHTML=function(kno)
{
  var prefix=false;
  if ((kno) && (kno!=this)) prefix=kno.name;
  var result; var dterm=this.dterm;
  if (!(dterm)) {
    fdjtWarn("toHTML called on invalid DTerm %o",this);
    result=fdjtSpan("dterm","????");}
  else if (this.dterm_base)
    result=fdjtSpan("dterm",this.dterm_base,
		    fdjtSpan("disambig",this.dterm_disambig));
  else {
    if (!(dterm.indexOf)) {
      fdjtWarn("bad dterm %o from %o",dterm,this);
      result=fdjtSpan("dterm",this.toString());}
    var colonpos=dterm.indexOf(':');
    if ((colonpos>0) && (colonpos<(dterm.length-1))) {
      if (dterm.slice(colonpos+1).search(/\w/)===0)
	result=fdjtSpan("dterm",dterm.slice(0,colonpos),
			fdjtSpan("dismabig",dterm.slice(colonpos)));
      else result=fdjtSpan("dterm",dterm);}
    else result=fdjtSpan("dterm",dterm);}
  result.knowde=this;
  if (prefix)
    result.setAttribute("dterm",dterm+"@"+prefix);
  else result.setAttribute("dterm",dterm);
  return result;
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

var kno_dterm_prefix=false;
var kno_dterm_suffix=false;

function knoSpan(dterm,display,kno)
{
  if (display instanceof KnowletType) {
    kno=display; display=false;}
  if ((kno!==false) && (!(kno))) kno=knowlet;
  if ((kno) && (typeof dterm === "string")) 
    if (dterm.indexOf('|')<0)
      dterm=kno.Knowde(dterm)||dterm;
    else dterm=kno.handleSubjectEntry(dterm).dterm;
  if (!(display))
    if (typeof dterm==='string')
      display=dterm;
    else display=dterm.dterm;
  var span=fdjtSpan("dterm",kno_dterm_prefix,display,kno_dterm_suffix);
  if (typeof dterm==='string') {
    span.setAttribute("dterm",dterm);
    span.dterm=dterm; span.knowde=false;}
  else {
    span.setAttribute("dterm",dterm.dterm);
    if (dterm.gloss) span.title=fdjtStripMarkup(dterm.gloss);
    span.dterm=dterm.dterm; span.knowde=dterm;}
  return span;
}
function knoDTermSpan(dterm,display,kno)
{
  return knoSpan(dterm,kno);
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
  if (typeof elt === "string")
    if (elt.indexOf('|')>0) {
      var knowde=knowlet.handleEntry(elt);
      if (knowde)
	return KnowdeRichTip(knowde);}
    else {
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
  else if ((elt instanceof Node) && (elt.knowde))
    return KnowdeRichTip(elt.knowde);
  else if ((elt instanceof Node) && (elt.getAttribute('dterm'))) {
    var dterm=elt.getAttribute('dterm');
    return KnowdeRichTip(elt.getAttribute('dterm'));}
  else return false;
}

fdjt_richtip_classfns["dterm"]=KnowdeRichTip;

/* Extended form elements for Knowdes */

function knoCheckspan(varname,value,checked,kno)
{
  var tagstring=knoTagString(value,kno||knowlet);
  var checkbox=fdjtInput("CHECKBOX",varname,value);
  var checkspan=fdjtSpan("checkspan",checkbox,knoSpan(value,kno||knowlet));
  if (checked) {
    checkspan.setAttribute('ischecked','true');
    checkbox.checked=true;}
  else {
    checkbox.checked=false;}
  return checkspan;
}

function knoCompletion(value,kno)
{
  var tagstring=knoTagString(value,kno||knowlet);
  var knospan=knoSpan(value,false,kno||knowlet);
  var dterm=(value.dterm)||value;
  fdjtAddClass(knospan,"completion");
  knospan.knowde=value; knospan.value=tagstring; knospan.key=dterm;
  var synonyms=value.terms;
  if (synonyms) {
    var i=0; while (i<synonyms.length) {
      var synonym=synonyms[i++];
      if (synonym===dterm) continue;
      var variant=fdjtSpan("variation",synonym,"=");
      variant.key=synonym;
      fdjtPrepend(knospan,variant);}}
  return knospan;
}

function knoCheckCompletion(varname,value,checked,kno)
{
  var checkspan=knoCompletion(value);
  var tagstring=knoTagString(value,kno||knowlet);
  var checkbox=fdjtInput("CHECKBOX",varname,value);
  checkbox.checked=checked||false;
  fdjtAddClass(checkspan,"checkspan");
  fdjtPrepend(checkspan,checkbox);
  fdjtCheckSpan_setup(checkspan);
  return checkspan;
}

/* Tag Tools */

function knoTagTool_addtag(tagpicks,varname,value,checked)
{
  if (typeof checked==='undefined') checked=true;
  var tagstring=((typeof value === 'string')?(value):(knoTagString(value)));
  var inputs=fdjtGetChildrenByClassName(tagpicks,'INPUT');
  var i=0; while (i<inputs.length) {
    var input=inputs[i++];
    if ((input.name===varname) &&
	((input.type==='checkbox')||(input.type==='radio')))
      if (input.value===tagstring) {
	var checkspan=$P(".checkspan",input);
	if (checkspan)
	  if (checked) checkspan.setAttribute('ischecked','yes');
	  else checkspan.setAttribute('ischecked','no');
	if (checked) input.checked=true; else input.checked=false;
	return false;}}
  var checkspan=knoCheckspan(varname,value,true);
  fdjtAppend(tagpicks," ",checkspan);
  return checkspan;
}

function knoTagTool_oncomplete(completion,value)
{
  var tagtool=$P(".tagtool",completion);
  var varname=((tagtool.varname)||(fdjtCacheAttrib(tagtool,'varname'))||'TAGS');
  var tagpicks=((tagtool.tagpicks)||(fdjtCacheAttrib(tagtool,'tagpicks',$$))||
		(fdjtGetChildrenByClassName(tagtool,'tagpicks')));
  if (!(tagpicks)) return;
  if (!(tagtool.tagpicks)) tagtool.tagpicks=tagpicks;
  knoTagTool_addtag(tagpicks,varname,completion.knowde,true);
  completion.setAttribute('suppressed','yes');
  this.value=""; fdjtComplete(this,"");
}

function knoTagTool_onkeypress(evt)
{
  evt=evt||event||null;
  var kc=evt.keyCode;
  var target=$T(evt);
  if (kc===13) {
    evt.cancelBubble=true;
    if (evt.preventDefault) evt.preventDefault(); else evt.returnValue=false;
    var tagtool=$P(".tagtool",target);
    var varname=
      ((tagtool.varname)||(fdjtCacheAttrib(tagtool,'varname'))||'TAGS');
    var tagpicks=
      ((tagtool.tagpicks)||(fdjtCacheAttrib(tagtool,'tagpicks',$$))||
       (fdjtGetChildrenByClassName(tagtool,'tagpicks')));
    var completions=fdjtComplete(target); var forced=false;
    if (completions.string==="") return false;
    if (completions.exactheads.length)
      forced=completions.exactheads[0];
    if (forced) 
      fdjtHandleCompletion(target,forced);
    else knoTagTool_addtag(tagpicks,varname,target.value,true);
    target.value="";
    return false;}
  else return fdjtComplete_onkey(evt);
}

function knoTagTool(varname,cueinit,cues,tvinit,tagverse)
{
  var tagpicks=fdjtDiv("tagpicks");
  tagpicks.onclick=fdjtCheckSpan_onclick;
  tagpicks.onchange=fdjtCheckSpan_onchange;
  var input=fdjtInput("TEXT",varname,"");
  var cues_elt=fdjtNewElt(cueinit||"span.tagcues");
  var tagverse_elt=fdjtNewElt(tvinit||"span.tagverse");
  var i=0; while (i<cues.length) 
	     fdjtAppend(cues_elt,knoCompletion(cues[i++])," ");
  knoAddTagverse(tagverse,tagverse_elt);
  var completions=fdjtDiv("completions",cues_elt,tagverse_elt);
  var tagtool=fdjtDiv("tagtool",tagpicks,input,completions);
  input.completions_elt=completions;
  completions.input_elt=input;

  completions.onclick=fdjtComplete_onclick;

  fdjtAddClass(input,"autoprompt");
  fdjtAddClass(input,"taginput");
  input.oncomplete=knoTagTool_oncomplete;
  input.onkeypress=knoTagTool_onkeypress;
  input.onfocus=fdjtAutoPrompt_onfocus;
  input.onblur=fdjtAutoPrompt_onblur;
  input.prompt="add a tag";
  input.completeopts=
    FDJT_COMPLETE_OPTIONS|FDJT_COMPLETE_ANYWORD|
    FDJT_COMPLETE_CLOUD;

  tagtool.tagpicks=tagpicks;
  tagtool.varname=varname;
  tagtool.setAttribute("VARNAME",varname);
  return tagtool;
}

function tagtool_termsort(t1,t2)
{
  if (typeof t1 === "string")
    if (typeof t2 === "string") {
      var l1=t1.toLowerCase(); var l2=t2.toLowerCase();
      if (l1<l2) return -1;
      else if (l1===l2)
	if (t1<t2) return -1; else if (t1===t2) return 0; else return 1;
      else return 1;}
    else return 1;
  else return -1;
}

function knoAddTagverse(tagverse,tagverse_elt)
{
  if (tagverse instanceof Array) {
    var termvec=[].concat(tagverse);
    termvec.sort();
    var i=0; while (i<termvec.length) {
      var term=termvec[i++]; var knowde=KnowdeProbe(term);
      if (!(knowde)) continue;
      fdjtAppend(tagverse_elt,knoCompletion(knowde)," ");}}
  else if (tagverse._all) {
    var all=tagverse._all; var termvec=[];
    var max=1; var logmax=0; var i=0; while (i<all.length) {
      var key=all[i++]; var val=tagverse[key];
      var knowde=KnowdeProbe(key);
      if (!(knowde)) continue;
      termvec.push(key);
      if (typeof val === "number") {
	if (val>max) max=val;}
      else if (val instanceof Array) {
	if (val.length>max) max=val.length;}}
    logmax=Math.log(max);
    termvec.sort(tagtool_termsort);
    i=0; while (i<termvec.length) {
      var term=termvec[i++]; var knowde=Knowde(term);
      var completion=knoCompletion(knowde);
      var val=tagverse[term]; var score=0;
      if (typeof val === "number") score=val;
      else if (typeof val === "string") score=1;
      else if (val.length) score=val.length;
      else score=1;
      completion.style.fontSize=((100)+100*(Math.sqrt(score)/logmax))+"%";
      fdjtAppend(tagverse_elt,completion," ");}}
}

/* Getting Knowlets out of HTML */

var _knowletsHTML_done=false;

function KnowletLoad(elt)
{
  var text=fdjtAjaxGetText(elt.src);
  var knowdes=knowlet.handleEntries(text);
  if (knowlets_trace_load)
    fdjtLog("[%fs] Parsed %d entries from %s",fdjtET(),knowdes.length,elt.src);
  if (elt.text) {
    var more_knowdes=knowlet.handleEntries(elt.text);
    if (knowlets_trace_load)
      fdjtLog("[%fs] Parsed %d more entries from %s",fdjtET(),knowdes.length);}
}

function knoHTMLSetup(node)
{
  var doing_the_whole_thing=false;
  var start=new Date();
  if ((!(node)) || (node_arg===document))
    if (_knowletsHTML_done) return;
    else {
      if (!(node)) {
	node=document;
	doing_the_whole_thing=true;}
      else if (node===document)
	doing_the_whole_thing=true;}
  var refuri=false;
  var elts=fdjtGetChildrenByTagName(document,"META");
  var i=0; while (i<elts.length) {
    var elt=elts[i++];
    if (elt.name==="KNOWLET") {
      knowlet=Knowlet(elt.content); break;}
    else if (elt.name==="REFURI") {
      refuri=elt.content;}}
  if ((!(knowlet)) && (refuri)) {
    if (knowlets_trace_load)
      fdjtLog("[%fs] Using REFURI '%s' as the name of the default knowlet",fdjtET(),refuri);
    knowlet=Knowlet(refuri);}
  if ((!(knowlet)) &&
      (document) && (document.location) &&
      (document.location.href)) {
    var url=document.location.href;
    var hash=url.indexOf("#");
    if (hash>=0) url=url.slice(0,hash);
    if (knowlets_trace_load)
      fdjtLog("[%fs] Using '%s' as the name of the default knowlet",fdjtET(),url);
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
	(((elt.getAttribute("language"))==="knowlet") ||
	 ((elt.getAttribute("language"))==="KNOWLET"))) {
      if (elt.src) KnowletLoad(elt);
      else if (elt.text) {
	var knowdes=knowlet.handleEntries(elt.text);
	if (knowlets_trace_load)
	  fdjtLog("[%fs] Parsed %d entries from %o",fdjtET(),knowdes.length,elt);}
      else {}}}
  var finished=new Date();
  if (knowlets_trace_load)
    fdjtLog("[%fs] Processed knowlets in ",
	    ((finished.getTime()-start.getTime())/1000)+"s",
	    fdjtET());
  if (doing_the_whole_thing) _knowletsHTML_done=true;
}

fdjtAddSetup(knoHTMLSetup);

/* Emacs local variables
;;;  Local variables: ***
;;;  compile-command: "cd ..; make" ***
;;;  End: ***
*/
