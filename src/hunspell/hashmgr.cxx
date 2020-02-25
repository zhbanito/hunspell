/* ***** BEGIN LICENSE BLOCK *****
 * Version: MPL 1.1/GPL 2.0/LGPL 2.1
 *
 * Copyright (C) 2002-2017 Németh László
 *
 * The contents of this file are subject to the Mozilla Public License Version
 * 1.1 (the "License"); you may not use this file except in compliance with
 * the License. You may obtain a copy of the License at
 * http://www.mozilla.org/MPL/
 *
 * Software distributed under the License is distributed on an "AS IS" basis,
 * WITHOUT WARRANTY OF ANY KIND, either express or implied. See the License
 * for the specific language governing rights and limitations under the
 * License.
 *
 * Hunspell is based on MySpell which is Copyright (C) 2002 Kevin Hendricks.
 *
 * Contributor(s): David Einstein, Davide Prina, Giuseppe Modugno,
 * Gianluca Turconi, Simon Brouwer, Noll János, Bíró Árpád,
 * Goldman Eleonóra, Sarlós Tamás, Bencsáth Boldizsár, Halácsy Péter,
 * Dvornik László, Gefferth András, Nagy Viktor, Varga Dániel, Chris Halls,
 * Rene Engelhard, Bram Moolenaar, Dafydd Jones, Harri Pitkänen
 *
 * Alternatively, the contents of this file may be used under the terms of
 * either the GNU General Public License Version 2 or later (the "GPL"), or
 * the GNU Lesser General Public License Version 2.1 or later (the "LGPL"),
 * in which case the provisions of the GPL or the LGPL are applicable instead
 * of those above. If you wish to allow use of your version of this file only
 * under the terms of either the GPL or the LGPL, and not to allow others to
 * use your version of this file under the terms of the MPL, indicate your
 * decision by deleting the provisions above and replace them with the notice
 * and other provisions required by the GPL or the LGPL. If you do not delete
 * the provisions above, a recipient may use your version of this file under
 * the terms of any one of the MPL, the GPL or the LGPL.
 *
 * ***** END LICENSE BLOCK ***** */
/*
 * Copyright 2002 Kevin B. Hendricks, Stratford, Ontario, Canada
 * And Contributors.  All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * 3. All modifications to the source code must be clearly marked as
 *    such.  Binary redistributions based on modified source code
 *    must be clearly marked as modified versions in the documentation
 *    and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY KEVIN B. HENDRICKS AND CONTRIBUTORS
 * ``AS IS'' AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
 * FOR A PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL
 * KEVIN B. HENDRICKS OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,
 * BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 */

#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <ctype.h>
#include <limits>

#include "hashmgr.hxx"
#include "csutil.hxx"
#include "atypes.hxx"
#include "langnum.hxx"

// build a hash table from a munched word list

HashMgr::HashMgr(const char* tpath, AffixMgr& aff, const char* key, int dic_data_len)
    : tablesize(0),
      tableptr(NULL),
      complexprefixes(0),
      utf8(0),
      forbiddenword(FORBIDDENWORD),  // forbidden word signing flag
      aff_mgr(&aff) {
  langnum = 0;
  csconv = 0;
  DataMgr* file = nullptr;
  if(dic_data_len == 0)
    file = new FileMgr(tpath, key);
  else
    file = new MemStrMgr(tpath, dic_data_len);
  int ec = load_tables(*file, *aff_mgr, key);
  if (ec) {
    /* error condition - what should we do here */
    HUNSPELL_WARNING(stderr, "Hash Manager Error : %d\n", ec);
    free(tableptr);
    //keep tablesize to 1 to fix possible division with zero
    tablesize = 1;
    tableptr = (struct hentry**)calloc(tablesize, sizeof(struct hentry*));
    if (!tableptr) {
      tablesize = 0;
    }
  }
  delete file;
}

HashMgr::~HashMgr() {
  if (tableptr) {
    // now pass through hash table freeing up everything
    // go through column by column of the table
    for (int i = 0; i < tablesize; i++) {
      struct hentry* pt = tableptr[i];
      struct hentry* nt = NULL;
      while (pt) {
        nt = pt->next;
        if (pt->astr &&
            (!aff_mgr->is_aliasf() || TESTAFF(pt->astr, ONLYUPCASEFLAG, pt->alen)))
          free(pt->astr);
        free(pt);
        pt = nt;
      }
    }
    free(tableptr);
  }
  tablesize = 0;

#ifndef OPENOFFICEORG
#ifndef MOZILLA_CLIENT
  if (utf8)
    free_utf_tbl();
#endif
#endif

#ifdef MOZILLA_CLIENT
  delete[] csconv;
#endif
}

// lookup a root word in the hashtable

struct hentry* HashMgr::lookup(const char* word) const {
  struct hentry* dp;
  if (tableptr) {
    dp = tableptr[hash(word)];
    if (!dp)
      return NULL;
    for (; dp != NULL; dp = dp->next) {
      if (strcmp(word, dp->word) == 0)
        return dp;
    }
  }
  return NULL;
}

// add a word to the hash table (private)
int HashMgr::add_word(const std::string& in_word,
                      int wcl,
                      unsigned short* aff,
                      int al,
                      const std::string* in_desc,
                      bool onlyupcase,
                      int captype) {
  const std::string* word = &in_word;
  const std::string* desc = in_desc;

  std::string *word_copy = NULL;
  std::string *desc_copy = NULL;
  if ((!ignorechars.empty() && !has_no_ignored_chars(in_word, ignorechars)) || complexprefixes) {
    word_copy = new std::string(in_word);

    if (!ignorechars.empty()) {
      if (utf8) {
        wcl = remove_ignored_chars_utf(*word_copy, ignorechars_utf16);
      } else {
        remove_ignored_chars(*word_copy, ignorechars);
      }
    }

    if (complexprefixes) {
      if (utf8)
        wcl = reverseword_utf(*word_copy);
      else
        reverseword(*word_copy);

      if (in_desc && !aff_mgr->is_aliasm()) {
        desc_copy = new std::string(*in_desc);

        if (complexprefixes) {
          if (utf8)
            reverseword_utf(*desc_copy);
          else
            reverseword(*desc_copy);
        }
        desc = desc_copy;
      }
    }

    word = word_copy;
  }

  bool upcasehomonym = false;
  int descl = desc ? (aff_mgr->is_aliasm() ? sizeof(char*) : desc->size() + 1) : 0;
  // variable-length hash record with word and optional fields
  struct hentry* hp =
      (struct hentry*)malloc(sizeof(struct hentry) + word->size() + descl);
  if (!hp) {
    delete desc_copy;
    delete word_copy;
    return 1;
  }

  char* hpw = hp->word;
  strcpy(hpw, word->c_str());

  int i = hash(hpw);

  hp->blen = (unsigned char)word->size();
  hp->clen = (unsigned char)wcl;
  hp->alen = (short)al;
  hp->astr = aff;
  hp->next = NULL;
  hp->next_homonym = NULL;
  hp->var = (captype == INITCAP) ? H_OPT_INITCAP : 0;

  // store the description string or its pointer
  if (desc) {
    hp->var += H_OPT;
    if (aff_mgr->is_aliasm()) {
      hp->var += H_OPT_ALIASM;
      store_pointer(hpw + word->size() + 1, aff_mgr->get_aliasm(atoi(desc->c_str())));
    } else {
      strcpy(hpw + word->size() + 1, desc->c_str());
    }
    if (strstr(HENTRY_DATA(hp), MORPH_PHON)) {
      hp->var += H_OPT_PHON;
      // store ph: fields (pronounciation, misspellings, old orthography etc.)
      // of a morphological description in reptable to use in REP replacements.
      if (aff_mgr->get_reptable().capacity() < (unsigned int)(tablesize/MORPH_PHON_RATIO))
          aff_mgr->get_reptable().reserve(tablesize/MORPH_PHON_RATIO);
      std::string fields = HENTRY_DATA(hp);
      std::string::const_iterator iter = fields.begin();
      std::string::const_iterator start_piece = mystrsep(fields, iter);
      while (start_piece != fields.end()) {
        if (std::string(start_piece, iter).find(MORPH_PHON) == 0) {
          std::string ph = std::string(start_piece, iter).substr(sizeof MORPH_PHON - 1);
          if (ph.size() > 0) {
            std::vector<w_char> w;
            size_t strippatt;
            std::string wordpart;
            // dictionary based REP replacement, separated by "->"
            // for example "pretty ph:prity ph:priti->pretti" to handle
            // both prity -> pretty and pritier -> prettiest suggestions.
            if (((strippatt = ph.find("->")) != std::string::npos) &&
                    (strippatt > 0) && (strippatt < ph.size() - 2)) {
                wordpart = ph.substr(strippatt + 2);
                ph.erase(ph.begin() + strippatt, ph.end());
            } else
                wordpart = in_word;
            // when the ph: field ends with the character *,
            // strip last character of the pattern and the replacement
            // to match in REP suggestions also at character changes,
            // for example, "pretty ph:prity*" results "prit->prett"
            // REP replacement instead of "prity->pretty", to get
            // prity->pretty and pritiest->prettiest suggestions.
            if (ph.at(ph.size()-1) == '*') {
              strippatt = 1;
              size_t stripword = 0;
              if (utf8) {
                while ((strippatt < ph.size()) &&
                  ((ph.at(ph.size()-strippatt-1) & 0xc0) == 0x80))
                     ++strippatt;
                while ((stripword < wordpart.size()) &&
                  ((wordpart.at(wordpart.size()-stripword-1) & 0xc0) == 0x80))
                     ++stripword;
              }
              ++strippatt;
              ++stripword;
              if ((ph.size() > strippatt) && (wordpart.size() > stripword)) {
                ph.erase(ph.size()-strippatt, strippatt);
                wordpart.erase(in_word.size()-stripword, stripword);
              }
            }
            // capitalize lowercase pattern for capitalized words to support
            // good suggestions also for capitalized misspellings, eg.
            // Wednesday ph:wendsay
            // results wendsay -> Wednesday and Wendsay -> Wednesday, too.
            if (captype==INITCAP) {
              std::string ph_capitalized;
              if (utf8) {
                u8_u16(w, ph);
                if (get_captype_utf8(w, langnum) == NOCAP) {
                  mkinitcap_utf(w, langnum);
                  u16_u8(ph_capitalized, w);
                }
              } else if (get_captype(ph, csconv) == NOCAP)
                  mkinitcap(ph_capitalized, csconv);

              if (ph_capitalized.size() > 0) {
                // add also lowercase word in the case of German or
                // Hungarian to support lowercase suggestions lowercased by
                // compound word generation or derivational suffixes
                // (for example by adjectival suffix "-i" of geographical
                // names in Hungarian:
                // Massachusetts ph:messzecsuzec
                // messzecsuzeci -> massachusettsi (adjective)
                // For lowercasing by conditional PFX rules, see
                // tests/germancompounding test example or the
                // Hungarian dictionary.)
                if (langnum == LANG_de || langnum == LANG_hu) {
                  std::string wordpart_lower(wordpart);
                  if (utf8) {
                    u8_u16(w, wordpart_lower);
                    mkallsmall_utf(w, langnum);
                    u16_u8(wordpart_lower, w);
                  } else {
                    mkallsmall(wordpart_lower, csconv);
                  }
                  aff_mgr->get_reptable().push_back(replentry());
                  aff_mgr->get_reptable().back().pattern.assign(ph);
                  aff_mgr->get_reptable().back().outstrings[0].assign(wordpart_lower);
                }
                aff_mgr->get_reptable().push_back(replentry());
                aff_mgr->get_reptable().back().pattern.assign(ph_capitalized);
                aff_mgr->get_reptable().back().outstrings[0].assign(wordpart);
              }
            }
            aff_mgr->get_reptable().push_back(replentry());
            aff_mgr->get_reptable().back().pattern.assign(ph);
            aff_mgr->get_reptable().back().outstrings[0].assign(wordpart);
          }
        }
        start_piece = mystrsep(fields, iter);
      }
    }
  }

  struct hentry* dp = tableptr[i];
  if (!dp) {
    tableptr[i] = hp;
    delete desc_copy;
    delete word_copy;
    return 0;
  }
  while (dp->next != NULL) {
    if ((!dp->next_homonym) && (strcmp(hp->word, dp->word) == 0)) {
      // remove hidden onlyupcase homonym
      if (!onlyupcase) {
        if ((dp->astr) && TESTAFF(dp->astr, ONLYUPCASEFLAG, dp->alen)) {
          free(dp->astr);
          dp->astr = hp->astr;
          dp->alen = hp->alen;
          free(hp);
          delete desc_copy;
          delete word_copy;
          return 0;
        } else {
          dp->next_homonym = hp;
        }
      } else {
        upcasehomonym = true;
      }
    }
    dp = dp->next;
  }
  if (strcmp(hp->word, dp->word) == 0) {
    // remove hidden onlyupcase homonym
    if (!onlyupcase) {
      if ((dp->astr) && TESTAFF(dp->astr, ONLYUPCASEFLAG, dp->alen)) {
        free(dp->astr);
        dp->astr = hp->astr;
        dp->alen = hp->alen;
        free(hp);
        delete desc_copy;
        delete word_copy;
        return 0;
      } else {
        dp->next_homonym = hp;
      }
    } else {
      upcasehomonym = true;
    }
  }
  if (!upcasehomonym) {
    dp->next = hp;
  } else {
    // remove hidden onlyupcase homonym
    if (hp->astr)
      free(hp->astr);
    free(hp);
  }

  delete desc_copy;
  delete word_copy;
  return 0;
}

int HashMgr::add_hidden_capitalized_word(const std::string& word,
                                         int wcl,
                                         unsigned short* flags,
                                         int flagslen,
                                         const std::string* dp,
                                         int captype) {
  if (flags == NULL)
    flagslen = 0;

  // add inner capitalized forms to handle the following allcap forms:
  // Mixed caps: OpenOffice.org -> OPENOFFICE.ORG
  // Allcaps with suffixes: CIA's -> CIA'S
  if (((captype == HUHCAP) || (captype == HUHINITCAP) ||
       ((captype == ALLCAP) && (flagslen != 0))) &&
      !((flagslen != 0) && TESTAFF(flags, forbiddenword, flagslen))) {
    unsigned short* flags2 =
        (unsigned short*)malloc(sizeof(unsigned short) * (flagslen + 1));
    if (!flags2)
      return 1;
    if (flagslen)
      memcpy(flags2, flags, flagslen * sizeof(unsigned short));
    flags2[flagslen] = ONLYUPCASEFLAG;
    if (utf8) {
      std::string st;
      std::vector<w_char> w;
      u8_u16(w, word);
      mkallsmall_utf(w, langnum);
      mkinitcap_utf(w, langnum);
      u16_u8(st, w);
      return add_word(st, wcl, flags2, flagslen + 1, dp, true, INITCAP);
    } else {
      std::string new_word(word);
      mkallsmall(new_word, csconv);
      mkinitcap(new_word, csconv);
      int ret = add_word(new_word, wcl, flags2, flagslen + 1, dp, true, INITCAP);
      return ret;
    }
  }
  return 0;
}

// detect captype and modify word length for UTF-8 encoding
int HashMgr::get_clen_and_captype(const std::string& word, int* captype, std::vector<w_char> &workbuf) {
  int len;
  if (utf8) {
    len = u8_u16(workbuf, word);
    *captype = get_captype_utf8(workbuf, langnum);
  } else {
    len = word.size();
    *captype = get_captype(word, csconv);
  }
  return len;
}

int HashMgr::get_clen_and_captype(const std::string& word, int* captype) {
  std::vector<w_char> workbuf;
  return get_clen_and_captype(word, captype, workbuf);
}

// remove word (personal dictionary function for standalone applications)
int HashMgr::remove(const std::string& word) {
  struct hentry* dp = lookup(word.c_str());
  while (dp) {
    if (dp->alen == 0 || !TESTAFF(dp->astr, forbiddenword, dp->alen)) {
      unsigned short* flags =
          (unsigned short*)malloc(sizeof(unsigned short) * (dp->alen + 1));
      if (!flags)
        return 1;
      for (int i = 0; i < dp->alen; i++)
        flags[i] = dp->astr[i];
      flags[dp->alen] = forbiddenword;
      free(dp->astr);
      dp->astr = flags;
      dp->alen++;
      std::sort(flags, flags + dp->alen);
    }
    dp = dp->next_homonym;
  }
  return 0;
}

/* remove forbidden flag to add a personal word to the hash */
int HashMgr::remove_forbidden_flag(const std::string& word) {
  struct hentry* dp = lookup(word.c_str());
  if (!dp)
    return 1;
  while (dp) {
    if (dp->astr && TESTAFF(dp->astr, forbiddenword, dp->alen))
      dp->alen = 0;  // XXX forbidden words of personal dic.
    dp = dp->next_homonym;
  }
  return 0;
}

// add a custom dic. word to the hash table (public)
int HashMgr::add(const std::string& word) {
  if (remove_forbidden_flag(word)) {
    int captype;
    int al = 0;
    unsigned short* flags = NULL;
    int wcl = get_clen_and_captype(word, &captype);
    add_word(word, wcl, flags, al, NULL, false, captype);
    return add_hidden_capitalized_word(word, wcl, flags, al, NULL,
                                       captype);
  }
  return 0;
}

int HashMgr::add_with_affix(const std::string& word, const std::string& example) {
  // detect captype and modify word length for UTF-8 encoding
  struct hentry* dp = lookup(example.c_str());
  remove_forbidden_flag(word);
  if (dp && dp->astr) {
    int captype;
    int wcl = get_clen_and_captype(word, &captype);
    if (aff_mgr->is_aliasf()) {
      add_word(word, wcl, dp->astr, dp->alen, NULL, false, captype);
    } else {
      unsigned short* flags =
          (unsigned short*)malloc(dp->alen * sizeof(unsigned short));
      if (flags) {
        memcpy((void*)flags, (void*)dp->astr,
               dp->alen * sizeof(unsigned short));
        add_word(word, wcl, flags, dp->alen, NULL, false, captype);
      } else
        return 1;
    }
    return add_hidden_capitalized_word(word, wcl, dp->astr,
                                       dp->alen, NULL, captype);
  }
  return 1;
}

// walk the hash table entry by entry - null at end
// initialize: col=-1; hp = NULL; hp = walk_hashtable(&col, hp);
struct hentry* HashMgr::walk_hashtable(int& col, struct hentry* hp) const {
  if (hp && hp->next != NULL)
    return hp->next;
  for (col++; col < tablesize; col++) {
    if (tableptr[col])
      return tableptr[col];
  }
  // null at end and reset to start
  col = -1;
  return NULL;
}

// load a munched word list and build a hash table on the fly
int HashMgr::load_tables(DataMgr& dict, const AffixMgr& aff_mgr, const char* key) {
  // first read the first line of file to get hash table size */
  std::string ts;
  if (!dict.getline(ts)) {
    HUNSPELL_WARNING(stderr, "error: empty dic file %s\n");
    return 2;
  }
  mychomp(ts);

  tablesize = atoi(ts.c_str());

  int nExtra = 5 + USERWORD;

  if (tablesize <= 0 ||
      (tablesize >= (std::numeric_limits<int>::max() - 1 - nExtra) /
                        int(sizeof(struct hentry*)))) {
    HUNSPELL_WARNING(
        stderr, "error: line 1: missing or bad word count in the dic file\n");
    return 4;
  }
  tablesize += nExtra;
  if ((tablesize % 2) == 0)
    tablesize++;

  // allocate the hash table
  tableptr = (struct hentry**)calloc(tablesize, sizeof(struct hentry*));
  if (!tableptr) {
    return 3;
  }

  // loop through all words on much list and add to hash
  // table and create word and affix strings

  std::vector<w_char> workbuf;

  while (dict.getline(ts)) {
    mychomp(ts);
    // split each line into word and morphological description
    size_t dp_pos = 0;
    while ((dp_pos = ts.find(':', dp_pos)) != std::string::npos) {
      if ((dp_pos > 3) && (ts[dp_pos - 3] == ' ' || ts[dp_pos - 3] == '\t')) {
        for (dp_pos -= 3; dp_pos > 0 && (ts[dp_pos-1] == ' ' || ts[dp_pos-1] == '\t'); --dp_pos)
          ;
        if (dp_pos == 0) {  // missing word
          dp_pos = std::string::npos;
        } else {
          ++dp_pos;
        }
        break;
      }
      ++dp_pos;
    }

    // tabulator is the old morphological field separator
    size_t dp2_pos = ts.find('\t');
    if (dp2_pos != std::string::npos && (dp_pos == std::string::npos || dp2_pos < dp_pos)) {
      dp_pos = dp2_pos + 1;
    }

    std::string dp;
    if (dp_pos != std::string::npos) {
      dp.assign(ts.substr(dp_pos));
      ts.resize(dp_pos - 1);
    }

    // split each line into word and affix char strings
    // "\/" signs slash in words (not affix separator)
    // "/" at beginning of the line is word character (not affix separator)
    size_t ap_pos = ts.find('/');
    while (ap_pos != std::string::npos) {
      if (ap_pos == 0) {
        ++ap_pos;
        continue;
      } else if (ts[ap_pos - 1] != '\\')
        break;
      // replace "\/" with "/"
      ts.erase(ap_pos - 1, 1);
      ap_pos = ts.find('/', ap_pos);
    }

    unsigned short* flags;
    int al;
    if (ap_pos != std::string::npos && ap_pos != ts.size()) {
      std::string ap(ts.substr(ap_pos + 1));
      ts.resize(ap_pos);
      if (this->aff_mgr->is_aliasf()) {
        int index = atoi(ap.c_str());
        al = this->aff_mgr->get_aliasf(index, &flags, dict);
        if (!al) {
          HUNSPELL_WARNING(stderr, "error: line %d: bad flag vector alias\n",
                           dict.getlinenum());
        }
      } else {
        al = this->aff_mgr->decode_flags(&flags, ap.c_str(), dict);
        if (al == -1) {
          HUNSPELL_WARNING(stderr, "Can't allocate memory.\n");
          return 6;
        }
        std::sort(flags, flags + al);
      }
    } else {
      al = 0;
      flags = NULL;
    }

    int captype;
    int wcl = get_clen_and_captype(ts, &captype, workbuf);
    const std::string *dp_str = dp.empty() ? NULL : &dp;
    // add the word and its index plus its capitalized form optionally
    if (add_word(ts, wcl, flags, al, dp_str, false, captype) ||
        add_hidden_capitalized_word(ts, wcl, flags, al, dp_str, captype)) {
      return 5;
    }
  }

  return 0;
}

// the hash function is a simple load and rotate
// algorithm borrowed
int HashMgr::hash(const char* word) const {
  unsigned long hv = 0;
  for (int i = 0; i < 4 && *word != 0; i++)
    hv = (hv << 8) | (*word++);
  while (*word != 0) {
    ROTATE(hv, ROTATE_LEN);
    hv ^= (*word++);
  }
  return (unsigned long)hv % tablesize;
}
