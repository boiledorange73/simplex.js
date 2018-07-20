/*
 * Simplex
 *
 * Internal data:
 *   tbl:
 *     Tableau. 2d numeric array.
 *     tbl = [
 *       ineq_1,
 *       ...
 *       ineq_N,
 *       object
 *     ]
 *     ineq_n = [x_1,...,x_M, s_1,...,s_N, c]
 *     object = [x_1,...,x_M,   0,...,  0, 0]
 *   bv:
 *     Basic Variables.
 *     1d [0,m) numeric vector.
 *     Each element is index of variables (including slack variables),
 *     so value of element is within [0,n).
 *   vn:
 *     Variable Name.
 *     d [0,m) string vector, each element is name of variable.
 *     vn[i] means name of xi.
 *
 * Static Function:
 *   LP.Simplex.create()
 *
 * Mathod:
 *   clear()
 *   putVN(string[])
 *   putAll(double[][])
 *   solve()
 *   answer()
 *   solve2()
 *
 */
(function(global) {
  if( !global["LP"] ) {
    global["LP"] = {};
  }

  var M = global["LP"];

  /*
   * Operators for each constraint inequation.
   */
  M.OP_LE = 0;
  M.OP_EQ = 1;
  M.OP_GE = 2;

  /*
   * Problem types.
   */
  M.PT_MAX = 0;
  M.PT_MIN = 1;

  /*
   * Constructor.
   *
   * @param tableaucols = Size of variables + Size of slack + 1 (Size of const)
   * @param tableaurows = SIze of inequations + 1 (object function)
   */
  M.Simplex = function(tableaucols, tableaurows, varslen) {
    this.tableaucols = tableaucols;
    this.tableaurows = tableaurows;
    this.ixr_object = tableaurows - 1;
    this.ixc_const = tableaucols - 1;
    this.varslen = varslen > 0 ? varslen : tableaucols - tableaurows; // cols-1-(rows-1)
    this.clear();
  };

  M.Simplex.ST_SOLVED = 0;
  M.Simplex.ST_UNBOUNDED = 1;
  M.Simplex.ST_NOTSOLVED = 2;

  // Clears all
  // @return this
  M.Simplex.prototype.clear = function() {
    this.tbl = []; // tableau
    this.bv = []; // basic variables
    this.vn = []; // variable name (human readable text)
    if( this.tableaucols > 0 && this.tableaurows > 0 ) {
      for(var nr = 0; nr < this.tableaurows; nr++ ) {
        // fills with zero.
        var row = new Array(this.tablecols);
        for(var nc = 0; nc < this.tableaucols; nc++ ) {
          row[nc] = 0;
        }
        // Adds row to tbl
        this.tbl[nr] = row;
      }
      // sets bv (basic variables)
      for(var nr = 0; nr < this.ixr_object; nr++ ) {
        this.bv[nr] = this.varslen + nr; // slack[nr]
      }
      this.bv[this.ixr_object] = -1; // at object function
      // sets vn
      for( var nc = 0; nc < this.varslen; nc++ ) {
        this.vn[nc] = "x"+(nc+1);
      }
      for( var nc = this.varslen; nc < this.ixc_const; nc++ ) {
        this.vn[nc] = "s"+(nc-this.varslen+1);
      }
      this.vn[this.ixc_const] = "c";
    }
    return this;
  };

  // Puts name of variables (without slack).
  // @param vn Array of variable names.
  // @return this
  M.Simplex.prototype.putVN = function(vn) {
    for(var n = 0; n < this.varslen; n++ ) {
      if( vn[n] !== null  || vn[n] !== undefined ) {
        this.vn[n] = ""+vn[n];
      }
    }
    return this;
  };

  // Puts a pure tableau. coefficients of an object function must be revered.
  // @param vn Array of array of tableau elements.
  // @return this
  M.Simplex.prototype.putAll = function(tableau) {
    for(var nr = 0; nr < this.tableaurows; nr++ ) {
      var row = this.tbl[nr];
      var row_t = tableau[nr];
      for(var nc = 0; nc < this.tableaucols; nc++ ) {
        row[nc] = row_t[nc];
      }
    }
    return this;
  }

  // LOCAL: an evaluation function for sort.
  function _fn_sort(a,b) {
    return a[0] - b[0];
  }

  // Solves.
  // @param iter Iterations. 15 by default.
  // @return Status code as following:
  //   0: Solved
  //   1: Unbounded:
  //   2: did not get optimized until specified iteration.
  M.Simplex.prototype.solve = function(iter) {
    if( !(iter > 0) ) {
      iter = 15;
    }
    while( iter-- > 0 ) {
      // finds pivot column
      var ixc = -1;
      var minval = 0;
      var vct = this.tbl[this.ixr_object];
      for(var nc = 0; nc < this.ixc_const; nc++ ) {
        if( vct[nc] < minval ) {
          minval = vct[nc];
          ixc = nc;
        }
      }
      if( ixc < 0 ) {
        // Gets optimized. Fin.
        return M.Simplex.ST_SOLVED;
      }
      // finds pivot row
      var ixr = -1;
      var minval = 0;
      for( var nr = 0; nr < this.ixr_object; nr++ ) {
        var vct = this.tbl[nr];
        var val = vct[this.ixc_const]/vct[ixc];
        if( val >= 0 && (ixr < 0 || val < minval) ) {
          minval = val;
          ixr = nr;
        }
      }
      if( ixr < 0 ) {
        // unbounded
        return M.Simplex.ST_UNBOUNDED;
      }
      //
      this.bv[ixr] = ixc;
      // [ixr][ixc]を1にする
      var vct = this.tbl[ixr];
      var val_c = vct[ixc];
      for( var nc = 0; nc < this.tableaucols; nc++ ) {
        vct[nc] = vct[nc]/val_c;
      }
      // 掃き出し
      for( var nr = 0; nr < this.tableaurows; nr++ ) {
        if( nr != ixr ) {
          var f = this.tbl[nr][ixc]/this.tbl[ixr][ixc];
          for( var nc = 0; nc < this.tableaucols; nc++ ) {
            this.tbl[nr][nc] -= this.tbl[ixr][nc] * f;
          }
        }
      }
    }
    return M.Simplex.ST_NOTSOLVED;
  };

  // Gets the answer after solve() called.
  // Returns a hash as following:
  //  "z": value of the object function.
  //  "values": array of variable (without slack) values,
  //    whose element contains [index, name of variable, value].
  //  "slacks": array of slack values,
  //    whose element contains [index, "s"+(index+1), value].
  // @return a hash contains "z", "values" and "slacks".
  M.Simplex.prototype.answer = function() {
    var z = null;
    var values = [];
    var slacks = [];
    for( var nr = 0; nr < this.tableaurows; nr++ ) {
      var ix = this.bv[nr];
      var v = this.tbl[nr][this.ixc_const];
      if( ix < 0 ) {
        z = v;
      }
      else {
        var one = [ix, this.vn[ix], v];
        if( ix < this.varslen ) {
          values.push(one);
        }
        else {
          slacks.push(one);
        }
      }
    }
    values = values.sort(_fn_sort);
    slacks = slacks.sort(_fn_sort);
    return {"z": z, "values": values, "slacks": slacks};
  };


// constraint:
//   coeffs: [a1, ..., an]
//   op: M.OP_LE
//   constant: c
// -> a1*x1+...+an*xn <= c
// objectfunction:
//   coeffs: [a1, ..., an]
//   ptype: LP.PT_MAX (default) or LP.PT_MIN
// -> maxz ->  z - (a1*x1+...+an*xn) = 0
// -> minz -> -z + (a1*x1+...+an*xn) = 0
  M.Constraint = function(coeffs, constant, op) {
    this.coeffs = coeffs;
    this.constant = constant;
    this.op = op;
  };

  M.ObjectFunction = function(coeffs, ptype) {
    this.coeffs = coeffs;
    this.ptype = ptype;
  };

  M.Simplex.create = function(constraints, objfn, vn) {
    var rowslen = constraints.length;
    // anmalyzes
    // counting slacks, max(count(variables))
    var varslen = 0;
    var slkslen = 0;
    for( var n_row = 0; n_row < rowslen; n_row++ ) {
      var row = constraints[n_row];
      var cols1 = row.coeffs.length;
      if( cols1 > varslen ) {
        varslen = cols1;
      }
      if( row.op == M.OP_LE || row.op == M.OP_GE ) {
        slkslen++;
      }
    }
    // tableaucols = Size of variables + Size of inequations (slack) + 1 (const)
    // tableaurows = SIze of inequations + 1 (object function)
    var ret = new M.Simplex(varslen+slkslen+1, rowslen+1);
    // puts all
    var n_slk = varslen;
    for( var n_row = 0; n_row < rowslen; n_row++ ) {
      var row = constraints[n_row];
      // coefficients
      for( var n_col = 0; n_col < varslen; n_col++ ) {
        ret.tbl[n_row][n_col] = row.coeffs[n_col];
      }
      // slack
      if( row.op == M.OP_LE ) {
        ret.tbl[n_row][n_slk] = 1;
        n_slk++;
      }
      else if( row.op == M.OP_GE ) {
        ret.tbl[n_row][n_slk] = -1;
        n_slk++;
      }
      // const
      ret.tbl[n_row][varslen+slkslen] = row.constant;
    }
    // objfn
    var fct = -1; // defaul (maximization)
    if( objfn.ptype == M.PT_MIN ) {
      fct = 1; // minimization
    }
    for( var n_col = 0; n_col < varslen; n_col++ ) {
      ret.tbl[rowslen][n_col] = fct * objfn.coeffs[n_col];
    }
    // vn (variable name)
    if( vn != null ) {
      ret.putVN(vn);
    }
    // fin
    return ret;
  }

  /**
   * Solves by 2 step solution
   */
  M.Simplex.prototype.solve2 = function() {
    var ieqslen = this.tableaurows-1; // size of inequations
    var s2 = new M.Simplex(this.tableaucols + ieqslen, this.tableaurows, this.tableaucols-1);
    // tableau
    for( var n_row = 0; n_row < s2.ixr_object; n_row++ ) {
      // coeffs
      for( var n_col = 0; n_col < s2.varslen; n_col++ ) {
        s2.tbl[n_row][n_col] = this.tbl[n_row][n_col];
      }
      // artifical variables
      s2.tbl[n_row][s2.varslen+n_row] = 1.0;
      // constant
      s2.tbl[n_row][s2.ixc_const] = this.tbl[n_row][this.ixc_const];
    }
    // W
    for( var n_col = s2.varslen; n_col < s2.ixc_const; n_col++ ) {
      s2.tbl[s2.ixr_object][n_col] = 1.0;
    }
    // Makes all coefficient for artifical variables into 0 at last row
    for( var n_col = 0; n_col < s2.tableaucols; n_col++ ) {
      for( var n_row = 0; n_row < s2.ixr_object; n_row++ ) {
        s2.tbl[s2.ixr_object][n_col] = s2.tbl[s2.ixr_object][n_col] - s2.tbl[n_row][n_col];
      }
    }
    // solve
    s2.solve();
    // brings tabuleau back to this, excepting last row (object function)
    for( var n_row = 0; n_row < this.ixr_object; n_row++ ) {
      for( var n_col = 0; n_col <= this.ixc_const; n_col++ ) {
        this.tbl[n_row][n_col] = s2.tbl[n_row][n_col];
      }
    }
    // brings constants back to this, excepting last row (object function)
    for( var n_row = 0; n_row < this.ixr_object; n_row++ ) {
      this.tbl[n_row][this.ixc_const] = s2.tbl[n_row][s2.ixc_const];
    }
    // brings bv (basic variables pointer) back to this, excepting last row (object function)
    for( var n_row = 0; n_row < this.ixr_object; n_row++ ) {
      this.bv[n_row] = s2.bv[n_row];
    }
    // solve
    this.solve();
  }

})((this || 0).self || global);

