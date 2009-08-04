/* -*- Mode: Javascript; -*- */

/* Copyright (C) 2009 beingmeta, inc.
   This file provides for browser-based tagging with knowlets.

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

/* A tagtool is tool for entering tags.  A tagtool is composed of
   four DOM components:
    tagpicks: a set of checkspans for the selected tags;
    taginput: a TEXT input element which completes over possible tags
     or allows other input;
    tagcues: a set of tag completions based on the thing being tagged
    tagverse: a set of tag completions drawn from a more general context

*/

function tagtoolAddTag(tagpicks,varname,value,checked)
{
  if (typeof checked==='undefined') checked=true;
  var inputs=fdjtFindChildrenByClassName(tagpicks,'INPUT');
  var i=0; while (i<inputs.length) {
    var input=inputs[i++];
    if ((input.name===varname) &&
	((input.type==='checkbox')||(input.type==='radio')))
      if (input.value===value) {
	var checkspan=$P(".checkspan",input);
	if (checkspan)
	  if (checked) checkspan.setAttribute('ischecked','yes');
	  else checkspan.setAttribute('ischecked','no');
	if (checked) input.checked=true; else input.checked=false;}}
  var checkspan=
    fdjtSpan('.checkspan',fdjtCheckbox(varname,value,true),
	     knoDtermSpan(value));
  fdjtAppend(tagpicks," ",checkspan);
  return checkspan;
}

function tagTool_oncomplete(evt,completion,value)
{
  var target=evt.target;
  var tagtool=$P(".tagtool",target);
  var varname=((tagtool.varname)||(fdjtCacheAttrib(tagtool,'varname'))||'TAGS');
  var tagpicks=((tagtool.tagpicks)||(fdjtCacheAttrib(tagtool,'tagpicks',$$))||
		(fdjtFindChildrenByClassName(tagtool,'tagpicks')));
  if (!(tagpicks)) return;
  if (!(tagtool.tagpicks)) tagtool.tagpicks=tagpicks;
  tagtoolAddTag(tagpicks,varname,value,true);
  completion.setAttribute('suppressed','yes');
}

function tagTool_onkey(evt)
{
  var kc=evt.keyCode;
  var target=evt.target;
  if (kc===13) {
    evt.cancelBubble=true; evt.preventDefault();
    var tagtool=$P(".tagtool",target);
    var varname=
      ((tagtool.varname)||(fdjtCacheAttrib(tagtool,'varname'))||'TAGS');
    var tagpicks=
      ((tagtool.tagpicks)||(fdjtCacheAttrib(tagtool,'tagpicks',$$))||
       (fdjtFindChildrenByClassName(tagtool,'tagpicks')));
    var completions=fdjtComplete(target); var forced=false;
    if (completions.string==="") return false;
    if (completions.exactheads.length)
      forced=completions.exactheads[0];
    if (forced) 
      fdjtHandleCompletion(target,forced);
    else tagtoolAddTag(tagpicks,varname,target.value,true);
    target.value="";
    return false;}
  else return fdjtComplete_onkey(evt);
}

function tagToolCreate(varname,cueinit,cues,tvinit,tagverse)
{
  var tagpicks=fdjtDiv("tagpicks");
  var input=fdjtInput("TEXT",varname,"");
  var cues_elt=fdjtNewElement(cueinit|"span.tagcues");
  var tagverse_elt=fdjtNewElement(tvinit|"span.tagverse");
  var completions=fdjtDiv("completions",cues_tagverse_elt);
  var i=0; while (i<cues.length) {}
  i=0; while (i<tagverse.length) {}
  var tagtool=fdjtDiv("tagtool",tagpicks,input,completions);
  input.completions_elt=completions;
  completions.input_elt=input;
  completions.onclick=fdjtComplete_onclick;
  input.oncomplete=tagTool_oncomplete;
  input.onkeypress=fdjtComplete_onkey;
  input.prompt="add a tag";
  tagtool.tagpicks=tagpicks;
  return tagtool;
}


