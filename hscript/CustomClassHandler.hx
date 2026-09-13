package hscript;

import hscript.Expr;
import hscript.utils.UnsafeReflect;

/**
 * Provides handlers for static custom class fields and instantiation.
 */
@:access(hscript.Property)
class CustomClassHandler implements IHScriptCustomConstructor implements IHScriptCustomAccessBehaviour{
	public var ogInterp:Interp;
	public var name:String;
	public var fields:Array<Expr>;
	public var extend:Null<String>;
	public var interfaces:Array<String>;
	public final isFinal:Bool;

	public var cl:Dynamic;

	private var __interp:Interp;
	private var __staticFields:Array<String> = [];

	public var __allowSetGet:Bool = true;

	public function new(ogInterp:Interp, name:String, fields:Array<Expr>, ?extend:String, ?interfaces:Array<String>, ?isFinal:Bool) {
		this.ogInterp = ogInterp;
		this.name = name;
		this.fields = fields;
		this.extend = extend;
		this.interfaces = interfaces;
		this.isFinal = isFinal != null ? isFinal : false;

		if(extend != null) {
			if(ogInterp.customClasses.exists(extend)) {
				var customCls:CustomClassHandler = ogInterp.customClasses.get(extend);
				if(customCls.isFinal)
					ogInterp.error(ECustom('Cannot extend a final class'));
				this.cl = customCls;
			}
			else 
				this.cl = Type.resolveClass('${extend}_HSX');

			if(cl == null)
				ogInterp.error(EInvalidClass(extend));
		}

		initStatic();
	}

	@:access(hscript.Interp)
	function initStatic() {
		__interp = new Interp();
		__interp.errorHandler = ogInterp.errorHandler;
		__interp.importFailedCallback = ogInterp.importFailedCallback;

		//__interp.variables = ogInterp.variables;
		__interp.usingHandler.usingEntries = ogInterp.usingHandler.usingEntries;
		__interp.usingHandler.hasUsingEntries = ogInterp.usingHandler.hasUsingEntries;
		__interp.publicVariables = ogInterp.publicVariables;
		__interp.staticVariables = ogInterp.staticVariables;
		__interp.customClasses = ogInterp.customClasses;

		for(f => v in ogInterp.variables) 
			if(!__interp.variables.exists(f))
				__interp.variables.set(f, v);

		for(i => e in fields.copy()) {
			var isValid:Bool = false;
			var staticField:Bool = false;
			var fieldName:String = null;
			var fieldRet:CType = null;
			var fieldMetas:Array<Dynamic> = null;
			var fieldExpr = Tools.expr(e);
			// Unwrap EMeta to extract per-field metadata (mirrors CustomClass.hx)
			while (fieldExpr.match(EMeta(_, _, _))) {
				switch(fieldExpr) {
					case EMeta(mname, margs, inner):
						if (fieldMetas == null) fieldMetas = [];
						var metaParams:Array<Dynamic> = null;
						if (margs != null) {
							metaParams = [];
							for (a in margs) metaParams.push(__interp.expr(a));
						}
						fieldMetas.push({ name: mname, params: metaParams });
						fieldExpr = Tools.expr(inner);
					default: break;
				}
			}
			switch (fieldExpr) {
				case EVar(n, _, _, _, isStatic):
					isValid = true;
					staticField = isStatic;
					fieldName = n;
				case EFunction(_, _, n, ret, _, isStatic):
					isValid = true;
					staticField = isStatic;
					fieldName = n;
					fieldRet = ret;
				default:
			}

			if(staticField && isValid) {
				__interp.exprReturn(e);
				__staticFields.push(fieldName);
				fields.remove(e);

				if (fieldMetas != null) {
					UnsafeReflect.setField(this, "__metas_" + fieldName, fieldMetas);
					for (m in fieldMetas) {
						if ((m.name == "to" || m.name == ":to") && fieldRet != null) {
							var targetType = new Printer().typeToString(fieldRet);
							var fn:Dynamic = __interp.variables.get(fieldName);
							if (fn != null) {
								var list:Array<Dynamic> = UnsafeReflect.field(this, "__conversions_to");
								if (list == null) {
									list = [];
									UnsafeReflect.setField(this, "__conversions_to", list);
								}
								list.push({ targetType: targetType, fn: fn });
							}
						}
						if (m.name == "from" || m.name == ":from") {
							var fn:Dynamic = __interp.variables.get(fieldName);
							if (fn != null) {
								var listFrom:Array<Dynamic> = UnsafeReflect.field(this, "__conversions_from");
								if (listFrom == null) {
									listFrom = [];
									UnsafeReflect.setField(this, "__conversions_from", listFrom);
								}
								listFrom.push({ fn: fn });
							}
						}
					}
				}
			}
		}
	}

	public function hnew(args:Array<Dynamic>):Dynamic 
		return new CustomClass(this, args);

	@:allow(hscript.Interp)
	inline function hasField(name:String) {
        return __staticFields.contains(name);
    }

	@:allow(hscript.Interp)
	function isNoUsing(name:String):Bool {
		var metas:Array<Dynamic> = UnsafeReflect.field(this, "__metas_" + name);
		if (metas == null) return false;
		for (m in metas)
			if (m.name == "noUsing" || m.name == ":noUsing") return true;
		return false;
	}

    function getField(name:String, allowProperty:Bool = true):Dynamic {
        var f = __interp.variables.get(name);
        if(f is Property && allowProperty) {
            var prop:Property = cast f;
            //prop.__allowSetGet = this.__allowSetGet;
            var r = prop.get(!__allowSetGet);
            //prop.__allowSetGet = true;
            return r;
        }
        return f;
    }

    function setField(name:String, val:Dynamic):Dynamic {
        var f = getField(name, false);
        if(f is Property) {
            var prop:Property = cast f;
            //prop.__allowSetGet = this.__allowSetGet;
            var r = prop.set(val, !__allowSetGet);
            //prop.__allowSetGet = true;
            return r;
        }
        __interp.variables.set(name, val);
        return val;
    }

	public function hget(name:String):Dynamic {
		if(name == 'new') {
			return Reflect.makeVarArgs(function(args:Array<Dynamic>):Dynamic {
				return inline this.hnew(args);
			});
		}
		
		if(hasField(name)) {
            return getField(name);
        }
		throw "field '"+ name+ "' does not exist in class '"+ this.name+ "'";
		return null;
	}

	public function hset(name:String, val:Dynamic):Dynamic {
		if(hasField(name))
			return setField(name, val);

		throw "field '"+ name+ "' does not exist in class '"+ this.name+ "'";
		return null;
	}

	// UNUSED
	public function __callGetter(name:String):Dynamic {
		return null;
	}

	public function __callSetter(name:String, val:Dynamic):Dynamic {
		return null;
	}

	public function toString():String {
		return name;
	}
}


/**
 * This is for backwards compatibility with old hscript-improved, since some scripts use it
**/
@:dox(hide)
@:keep
class TemplateClass implements IHScriptCustomBehaviour implements IHScriptCustomAccessBehaviour {
	public var __interp:Interp;
	public var __allowSetGet:Bool = true;

	public function hset(name:String, val:Dynamic):Dynamic {
		var variables = __interp.variables;
		if(__allowSetGet && variables.exists("set_" + name))
			return __callSetter(name, val);
		variables.set(name, val);
		return val;
	}
	public function hget(name:String):Dynamic {
		var variables = __interp.variables;
		if(__allowSetGet && variables.exists("get_" + name))
			return __callGetter(name);
		return variables.get(name);
	}

	public function __callGetter(name:String):Dynamic {
		__allowSetGet = false;
		var v = __interp.variables.get("get_" + name)();
		__allowSetGet = true;
		return v;
	}

	public function __callSetter(name:String, val:Dynamic):Dynamic {
		__allowSetGet = false;
		var v = __interp.variables.get("set_" + name)(val);
		__allowSetGet = true;
		return v;
	}
}