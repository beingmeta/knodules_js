/* -*- Mode: Javascript; -*- */

/* Copyright (C) 2009-2011 beingmeta, inc.
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

