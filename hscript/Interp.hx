/*
 * Copyright (C)2008-2017 Haxe Foundation
 *
 * Permission is hereby granted, free of charge, to any person obtaining a
 * copy of this software and associated documentation files (the "Software"),
 * to deal in the Software without restriction, including without limitation
 * the rights to use, copy, modify, merge, publish, distribute, sublicense,
 * and/or sell copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
 * DEALINGS IN THE SOFTWARE.
 */

/*
 * YoshiCrafter Engine fixes:
 * - Added Error handler
 * - Added Imports
 * - Added @:bypassAccessor
 */
package hscript;

import haxe.Exception;
import haxe.ds.StringMap;
import hscript.HEnum.HEnumValue;
import haxe.CallStack;
import hscript.utils.UsingHandler;
import hscript.utils.UnsafeReflect;
import haxe.PosInfos;
import hscript.Expr;
import haxe.Constraints.IMap;

using StringTools;

private enum Stop {
	SBreak;
	SContinue;
	SReturn;
}

enum abstract ScriptObjectType(UInt8) {
	var SClass;
	var SObject;
	var SStaticClass;
	var SCustomClass; // custom classes
	var SBehaviourClass; // hget and hset
	var SAccessBehaviourObject; // hget and hset with __allowSetGet
	var SNull;
}

enum abstract VarLocation(UInt8) {
	var VGlobal;
	var VPublic;
	var VStatic;
	var VScriptObject;
	var VScriptObjectGetter;
	var VCustomClass;
	var VCustomClassBypass;
	var VBehaviourClass;
	var VAccessBehaviour;
	var VAccessBehaviourBypass;
	var VNotFound;
}

@:structInit
class DeclaredVar {
	public var r:Dynamic;
	public var depth:Int;
	public var isFinal:Bool;
}

@:structInit
class RedeclaredVar {
	public var n:String;
	public var old:DeclaredVar;
	public var depth:Int;
}

@:access(hscript.CustomClass)
@:access(hscript.SScript)
@:analyzer(optimize, local_dce, fusion, user_var_fusion)
class Interp {
	private static var _EMPTY_ARGS:Array<Dynamic> = [];
	private var hasScriptObject(default, null):Bool = false;
	private var _scriptObjectType(default, null):ScriptObjectType = SNull;

	var __instanceFields:Map<String, Bool> = new Map();

	/** Converts an array of field names into a lookup map (O(1) membership checks). **/
	static inline function fieldsToMap(fields:Array<String>):Map<String, Bool> {
		var m:Map<String, Bool> = new Map();
		for (f in fields) m.set(f, true);
		return m;
	}

	public var scriptObject(default, set):Dynamic;
	public function set_scriptObject(v:Dynamic) {
		switch(Type.typeof(v)) {
			case TClass(c): // Class Access
				__instanceFields = fieldsToMap(Type.getInstanceFields(c));
				if(v is IHScriptCustomClassBehaviour) {
					var v:IHScriptCustomClassBehaviour = cast v;
					var classFields = v.__class__fields;
					if(classFields != null)
						for (f in classFields) __instanceFields.set(f, true);
					inCustomClass = true;
					_scriptObjectType = SCustomClass;
				} else if(v is IHScriptCustomAccessBehaviour) {
					_scriptObjectType = SAccessBehaviourObject;
				} else if(v is IHScriptCustomBehaviour) {
					_scriptObjectType = SBehaviourClass;
				} else {
					_scriptObjectType = SClass;
				}
			case TObject: // Object Access or Static Class Access
				var cls = Type.getClass(v);
				switch(Type.typeof(cls)) {
					case TClass(c): // Static Class Access
						__instanceFields = fieldsToMap(Type.getInstanceFields(c));
						_scriptObjectType = SStaticClass;
					default: // Object Access
						__instanceFields = fieldsToMap(Reflect.fields(v));
						_scriptObjectType = SObject;
				}
			default: // Null or other
				__instanceFields = new Map();
				_scriptObjectType = SNull;
		}
		hasScriptObject = v != null;
		return scriptObject = v;
	}

	var inCustomClass(default, null):Bool = false;

	var __customClass(get, never):CustomClass;
	private function get___customClass():CustomClass
		return inCustomClass ? cast scriptObject : null;

	public var errorHandler:Error->Void;
	public var warnHandler:Error->Void;
	// TODO: set this callback as a Global Resolver
	/**
	 * Custom Import resolver. It's called when an import couldn't be resolved.
	 */
	public var importFailedCallback:Array<String>->Null<String>->Bool;

	public var customClasses:Map<String, CustomClassHandler>;
	public var variables:Map<String, Dynamic>;
	public var publicVariables:Map<String, Dynamic>;
	// TODO: maybe turn this completely static
	public var staticVariables:Map<String, Dynamic>;

	// warning can be null
	public var locals:Map<String, DeclaredVar>;

	var depth:Int = 0;
	var blockDepth:Int = 0; // nesting level of `{ }` blocks; >1 means inside a nested block (not top-level)
	var inTry:Bool;
	var declared:Array<RedeclaredVar>;
	var returnValue:Dynamic;

	var isBypassAccessor:Bool = false;
	var setAlias:Null<String> = null; // Custom Class import alias
	var beforeAlias:Null<String> = null;

	public var importEnabled:Bool = true;
	public var allowStaticImports:Bool = true;

	public var allowStaticVariables:Bool = false;
	public var allowPublicVariables:Bool = false;

	public var importBlocklist(get, never):Array<String>;
	private inline function get_importBlocklist():Array<String> {
		return Config.IMPORT_BLACKLIST;
	}

	var usingHandler:UsingHandler;
	
	var script:SScript;
	public var specialObject:{obj:Dynamic, ?includeFunctions:Bool, ?exclusions:Array<String>} = {obj: null, includeFunctions: null, exclusions: null};

	public inline function setScr(s:SScript) {
		script = s;
	}
	// TODO: separate cache into a class
	var varLocationCache:Map<String, VarLocation> = [];
	/** Caches Type.resolveClass/resolveEnum results for VNotFound identifiers. Classes don't change at runtime, so this is safe to keep. **/
	var __typeResolveCache:Map<String, Dynamic> = [];
	public var cacheValid(default, set):Bool = true;
	function set_cacheValid(valid:Bool):Bool {
		return cacheValid = valid;
	}

	#if hscriptPos
	var curExpr:Expr;
	#end

	public function new() {
		locals = new Map();
		declared = [];
		resetVariables();
	}

	private function resetVariables():Void {
		customClasses = new Map<String, CustomClassHandler>();
		variables = new Map<String, Dynamic>();
		publicVariables = new Map<String, Dynamic>();
		staticVariables = new Map<String, Dynamic>();

		usingHandler = new UsingHandler();
		
		variables.set("null", null);
		variables.set("true", true);
		variables.set("false", false);
		variables.set("trace", Reflect.makeVarArgs(function(el) {
			var inf = posInfos();
			var v = el.shift();
			if (el.length > 0)
				inf.customParams = el;
			haxe.Log.trace(Std.string(v), inf);
		}));
	}

	public function posInfos():PosInfos {
		#if hscriptPos
		if (curExpr != null)
			return cast {fileName: curExpr.origin, lineNumber: curExpr.line};
		#end
		return cast {fileName: "hscript", lineNumber: 0};
	}

	function checkIsType(e1:Expr,e2:Expr): Bool {
		var expr1:Dynamic = expr(e1);

		return switch(Tools.expr(e2))
		{
			case EIdent("Class"):
				Std.isOfType(expr1, Class);
			case EIdent("Map") | EIdent("IMap"):
				Std.isOfType(expr1, IMap);
			default:
				var expr2:Dynamic = expr(e2);
				if(expr2 != null) {
					if(expr1 is CustomClass && expr2 is CustomClassHandler) {
						var objName = cast(expr1, CustomClass).className;
						var clsName = cast(expr2, CustomClassHandler).name;
						objName == clsName;
					}
					else 
						Std.isOfType(expr1, expr2);
				}
				else 
					false;
		}
	}

	public function varExists(name:String):Bool {
		return allowStaticVariables && staticVariables.exists(name) || allowPublicVariables && publicVariables.exists(name) || variables.exists(name);
	}

	public function setVar(name:String, v:Dynamic):Void {
		if (allowStaticVariables && staticVariables.exists(name))
			staticVariables.set(name, v);
		else if (allowPublicVariables && publicVariables.exists(name))
			publicVariables.set(name, v);
		else if (variables.exists(name))
			variables.set(name, v);
		else if (allowPublicVariables)
			// Truly new name in a pack that shares public vars: publish it so
			// sibling scripts declaring/reading it later resolve the same value
			// (fixes cross-script assignment made before the `public var` declaration runs).
			publicVariables.set(name, v);
		else
			variables.set(name, v);
	}

	function assign(e1:Expr, e2:Expr):Dynamic {
		var v = expr(e2);
		switch (Tools.expr(e1)) {
			case EIdent(id):
				var l = locals.get(id);
				if (l != null && l.isFinal)
					return error(ECustom('Cannot reassign final variable $id'));
				if (l == null) {
					// Fast path: write directly to the cached location, skipping the varExists/field-scan/resolve re-lookup.
					if (cacheValid) {
						var loc = varLocationCache.get(id);
						if (loc != null) {
							switch (loc) {
								case VGlobal:
									var cur = variables.get(id);
									if (cur is Property) return (cast cur:Property).set(v, isBypassAccessor);
									variables.set(id, v);
									return v;
								case VPublic:
									var cur = publicVariables.get(id);
									if (cur is Property) return (cast cur:Property).set(v, isBypassAccessor);
									publicVariables.set(id, v);
									return v;
								case VStatic:
									var cur = staticVariables.get(id);
									if (cur is Property) return (cast cur:Property).set(v, isBypassAccessor);
									staticVariables.set(id, v);
									return v;
								case VScriptObject:
									if (_scriptObjectType == SObject || isBypassAccessor) {
										UnsafeReflect.setField(scriptObject, id, v);
										return v;
									}
									UnsafeReflect.setProperty(scriptObject, id, v);
									return UnsafeReflect.field(scriptObject, id);
								case VCustomClassBypass:
									var obj:IHScriptCustomAccessBehaviour = cast scriptObject;
									obj.__allowSetGet = false;
									var res = obj.hset(id, v);
									obj.__allowSetGet = true;
									return res;
								case VCustomClass:
									return (cast scriptObject:IHScriptCustomAccessBehaviour).hset(id, v);
								case VAccessBehaviourBypass:
									var obj:IHScriptCustomAccessBehaviour = cast scriptObject;
									obj.__allowSetGet = false;
									var res = obj.hset(id, v);
									obj.__allowSetGet = true;
									return res;
								case VAccessBehaviour:
									return (cast scriptObject:IHScriptCustomAccessBehaviour).hset(id, v);
								case VBehaviourClass:
									return (cast scriptObject:IHScriptCustomBehaviour).hset(id, v);
								case VScriptObjectGetter, VNotFound:
									// fall back to the original slow path below
							}
						}
					}
					if (hasScriptObject && !varExists(id)) {
						var instanceHasField = __instanceFields.exists(id);

						if (_scriptObjectType == SObject && instanceHasField) {
							UnsafeReflect.setField(scriptObject, id, v);
							return v;
						} else if((_scriptObjectType == SCustomClass && instanceHasField) || _scriptObjectType == SAccessBehaviourObject) {
							var obj:IHScriptCustomAccessBehaviour = cast scriptObject;
							if(isBypassAccessor) {
								obj.__allowSetGet = false;
								var res = obj.hset(id, v);
								obj.__allowSetGet = true;
								return res;
							}
							return obj.hset(id, v);
						}
						else if (_scriptObjectType == SBehaviourClass) {
							var obj:IHScriptCustomBehaviour = cast scriptObject;
							return obj.hset(id, v);
						}

						if (instanceHasField) {
							if(isBypassAccessor) {
								UnsafeReflect.setField(scriptObject, id, v);
								return v;
							} else {
								UnsafeReflect.setProperty(scriptObject, id, v);
								return UnsafeReflect.field(scriptObject, id);
							}
						} else if (__instanceFields.exists('set_$id')) { // setter
							return UnsafeReflect.getProperty(scriptObject, 'set_$id')(v);
						} else {
							varLocationCache.remove(id);
							setVar(id, v);
						}
					} else {
						var obj = resolve(id, false, false);
						if (obj != null && obj is Property) {
							var prop:Property = cast obj;
							return prop.set(v, isBypassAccessor);
						}
						varLocationCache.remove(id);
						setVar(id, v);
					}
				} else if (l.r is Property) {
					var prop:Property = cast l.r;
					return prop.set(v, isBypassAccessor);
				} else {
					l.r = v;
					if (l.depth == 0)
						setVar(id, v);
				}
				// TODO
			case EField(e, f, s):
				var obj = expr(e);
				if(s && obj == null) return null;
				v = set(obj, f, v);
			case EArray(e, index):
				var arr:Dynamic = expr(e);
				var index:Dynamic = expr(index);
				var r = tryArrayAccessSet(arr, index, v);
				if (r != null) return r;
				if (isMap(arr)) {
					setMapValue(getMap(arr), index, v);
				} else {
					arr[index] = v;
				}

			default:
				error(EInvalidOp("="));
		}
		return v;
	}

	function evalAssignOp(op:Binop, fop:Dynamic->Dynamic->Dynamic, e1:Expr, e2:Expr):Dynamic {
		var v;
		switch (Tools.expr(e1)) {
			case EIdent(id):
				var l = locals.get(id);
				if (l != null && l.isFinal)
					return error(ECustom('Cannot reassign final variable $id'));
				v = fop(expr(e1), expr(e2));
				if (l == null) {
					// Fast path: write directly to the cached location (same semantics as the slow path below).
					if (cacheValid) {
						var loc = varLocationCache.get(id);
						if (loc != null) {
							switch (loc) {
								case VGlobal:
									var cur = variables.get(id);
									if (cur is Property) return (cast cur:Property).set(v, isBypassAccessor);
									variables.set(id, v);
									return v;
								case VPublic:
									var cur = publicVariables.get(id);
									if (cur is Property) return (cast cur:Property).set(v, isBypassAccessor);
									publicVariables.set(id, v);
									return v;
								case VStatic:
									var cur = staticVariables.get(id);
									if (cur is Property) return (cast cur:Property).set(v, isBypassAccessor);
									staticVariables.set(id, v);
									return v;
								case VScriptObject:
									if (_scriptObjectType == SObject || isBypassAccessor) {
										UnsafeReflect.setField(scriptObject, id, v);
										return v;
									}
									UnsafeReflect.setProperty(scriptObject, id, v);
									return UnsafeReflect.field(scriptObject, id);
								case VCustomClassBypass:
									var obj:IHScriptCustomAccessBehaviour = cast scriptObject;
									obj.__allowSetGet = false;
									var res = obj.hset(id, v);
									obj.__allowSetGet = true;
									return res;
								case VCustomClass:
									return (cast scriptObject:IHScriptCustomAccessBehaviour).hset(id, v);
								case VAccessBehaviourBypass:
									var obj:IHScriptCustomAccessBehaviour = cast scriptObject;
									obj.__allowSetGet = false;
									var res = obj.hset(id, v);
									obj.__allowSetGet = true;
									return res;
								case VAccessBehaviour:
									return (cast scriptObject:IHScriptCustomAccessBehaviour).hset(id, v);
								case VBehaviourClass:
									return (cast scriptObject:IHScriptCustomBehaviour).hset(id, v);
								case VScriptObjectGetter, VNotFound:
									// fall back to the original slow path below
							}
						}
					}
					if(hasScriptObject && !varExists(id)) {
						var instanceHasField = __instanceFields.exists(id);

						if (_scriptObjectType == SObject && instanceHasField) {
							UnsafeReflect.setField(scriptObject, id, v);
							return v;
						} else if((_scriptObjectType == SCustomClass && instanceHasField) || _scriptObjectType == SAccessBehaviourObject) {
							var obj:IHScriptCustomAccessBehaviour = cast scriptObject;
							if(isBypassAccessor) {
								obj.__allowSetGet = false;
								var res = obj.hset(id, v);
								obj.__allowSetGet = true;
								return res;
							}
							return obj.hset(id, v);
						}
						else if (_scriptObjectType == SBehaviourClass) {
							var obj:IHScriptCustomBehaviour = cast scriptObject;
							return obj.hset(id, v);
						}

						if (instanceHasField) {
							if(isBypassAccessor) {
								UnsafeReflect.setField(scriptObject, id, v);
								return v;
							} else {
								UnsafeReflect.setProperty(scriptObject, id, v);
								return UnsafeReflect.field(scriptObject, id);
							}
						} else if (__instanceFields.exists('set_$id')) { // setter
							return UnsafeReflect.getProperty(scriptObject, 'set_$id')(v);
						} else {
							varLocationCache.remove(id);
							setVar(id, v);
						}
					} else {
						var obj = resolve(id, true, false);
						if (obj != null && obj is Property) {
							var prop:Property = cast obj;
							return prop.set(v, isBypassAccessor);
						}
						varLocationCache.remove(id);
						setVar(id, v);
					}
				}
				else {
					if (l.r is Property) {
						var prop:Property = cast l.r;
						return prop.set(v, isBypassAccessor);
					}
					l.r = v;
				if (l.depth == 0)
					setVar(id, v);
				}
			case EField(e, f, s):
				var obj = expr(e);
				if(s && obj == null) return null;
				v = fop(get(obj, f), expr(e2));
				v = set(obj, f, v);
			case EArray(e, index):
				var arr:Dynamic = expr(e);
				var index:Dynamic = expr(index);
				if (arr is IHScriptAbstractBehaviour && cast(arr, IHScriptAbstractBehaviour).hasArr) {
					var cur = tryArrayAccessGet(arr, index);
					v = fop(cur, expr(e2));
					tryArrayAccessSet(arr, index, v);
				} else if (isMap(arr)) {
					var map = getMap(arr);
					v = fop(map.get(index), expr(e2));
					map.set(index, v);
				} else {
					v = fop(arr[index], expr(e2));
					arr[index] = v;
				}
			default:
				return error(EInvalidOp(op.toString()));
		}
		return v;
	}

	function increment(e:Expr, prefix:Bool, delta:Int):Dynamic {
		#if hscriptPos
		curExpr = e;
		var e = e.e;
		#end
		switch (e) {
			case EIdent(id):
				var l = locals.get(id);
				if(l != null) {
					if(l.isFinal)
						return error(ECustom('Cannot increment final variable $id'));
					var v:Dynamic = l.r;
					var prop:Property = null;
					if (v is Property) {
						prop = cast v;
						v = prop.get(isBypassAccessor);
					}

					if (prefix) {
						v += delta;
						if (prop != null)
							prop.set(v, isBypassAccessor);
						else
							l.r = v;
					} else {
						if (prop != null)
							prop.set(v + delta, isBypassAccessor);
						else
							l.r = v + delta;
					}
					return v;
				} else {
					var v:Dynamic = resolve(id, true, false);
					var prop:Property = null;
					if (v is Property) {
						prop = cast v;
						v = prop.get(isBypassAccessor);
					}

					if (prefix) {
						v += delta;
						if (prop != null)
							prop.set(v, isBypassAccessor);
						else if (!cachedSet(id, v)) {
							varLocationCache.remove(id);
							setVar(id, v);
						}
					} else {
						if (prop != null)
							prop.set(v + delta, isBypassAccessor);
						else if (!cachedSet(id, v + delta)) {
							varLocationCache.remove(id);
							setVar(id, v + delta);
						}
					}
					return v;
				}
			case EField(e, f, s):
				var obj = expr(e);
				if(s && obj == null) return null;
				var v:Dynamic = get(obj, f);
				if (prefix) {
					v += delta;
					set(obj, f, v);
				} else
					set(obj, f, v + delta);
				return v;
			case EArray(e, index):
				var arr:Dynamic = expr(e);
				var index:Dynamic = expr(index);
				if (isMap(arr)) {
					var map = getMap(arr);

					var v = map.get(index);
					if (prefix) {
						v += delta;
						map.set(index, v);
					} else {
						map.set(index, v + delta);
					}
					return v;
				} else {
					var v = arr[index];
					if (prefix) {
						v += delta;
						arr[index] = v;
					} else
						arr[index] = v + delta;
					return v;
				}
			default:
				return error(EInvalidOp((delta > 0) ? "++" : "--"));
		}
	}

	public function execute(expr:Expr):Dynamic {
		depth = 0;
		blockDepth = 0;
		locals = new Map();
		declared = [];
		return exprReturn(expr);
	}

	public var printCallStack:Bool = false;

	function exprReturn(e):Dynamic {
		try {
			return expr(e);
		} catch (e:Stop) {
			switch (e) {
				case SBreak:
					throw "Invalid break";
				case SContinue:
					throw "Invalid continue";
				case SReturn:
					var v = returnValue;
					returnValue = null;
					return v;
			}
		} catch (e:Error) {
			if (errorHandler != null) {
				errorHandler(e);
			} else {
				throw e;
			}
			return null;
		} catch (e:Dynamic) {
			var errStr = printCallStack ? Std.string(e) + "\n" + CallStack.toString(CallStack.exceptionStack(true)) : Std.string(e);
			if (errorHandler != null) {
				#if hscriptPos
				errorHandler(new Error(ECustom(errStr), curExpr.pmin, curExpr.pmax, curExpr.origin, curExpr.line));
				#else
				errorHandler(Error.ECustom(errStr));
				#end
			} else {
				throw e;
			}
			return null;
		}
		return null;
	}

	public function duplicate<T>(h:Map<String, T>) {
		var h2 = new Map();
		var keys = h.keys();
		var _hasNext = keys.hasNext;
		var _next = keys.next;
		while (_hasNext()) {
			var k = _next();
			h2.set(k, h.get(k));
		}
		return h2;
	}

	inline function restore(old:Int):Void {
		while (declared.length > old) {
			var d = declared.pop();
			locals.set(d.n, d.old);
		}
	}

	function matchPatternValue(p:Expr, v:Dynamic):Bool {
		return switch (Tools.expr(p)) {
			case EIdent("_"): true;
			case EIdent(n):
				declared.push({n: n, old: locals.get(n), depth: depth});
				locals.set(n, {r: v, depth: depth, isFinal: false});
				true;
			case EConst(CInt(i)): v == i;
			case EConst(CFloat(f)): v == f;
			case EConst(CString(s)): v == s;
			case EArrayDecl(elements):
				if (!(v is Array)) return false;
				return matchArrayPattern(cast v, elements);
			case EObject(fields):
				return matchObjectPattern(v, fields);
			default:
				expr(p) == v;
		}
	}

	function matchArrayPattern(val:Array<Dynamic>, elements:Array<Expr>):Bool {
		if (val.length != elements.length) return false;
		var saved = declared.length;
		for (i in 0...elements.length) {
			if (!matchPatternValue(elements[i], val[i])) {
				restore(saved);
				return false;
			}
		}
		return true;
	}

	function matchObjectPattern(val:Dynamic, fields:Array<ObjectField>):Bool {
		var saved = declared.length;
		for (f in fields) {
			var fieldVal = Reflect.field(val, f.name);
			if (!matchPatternValue(f.e, fieldVal)) {
				restore(saved);
				return false;
			}
		}
		return true;
	}

	function matchOrPattern(e:Expr, val:Dynamic):Bool {
		var tk = Tools.expr(e);
		return switch (tk) {
			case EBinop(OpOr, e1, e2):
				var saved = declared.length;
				if (matchOrPattern(e1, val)) true;
				else {
					restore(saved);
					matchOrPattern(e2, val);
				}
			default:
				matchPatternValue(e, val);
		}
	}

	public static function getMetas(val:Dynamic):Array<Dynamic> {
		return UnsafeReflect.field(val, "__metas");
	}

	public static function getMeta(val:Dynamic, name:String):Dynamic {
		var metas = getMetas(val);
		if(metas == null) return null;
		for(m in metas)
			if(m.name == name) return m.params;
		return null;
	}

	public static function hasMeta(val:Dynamic, name:String):Bool {
		return getMeta(val, name) != null;
	}

	function tryOpOverload(op:String, a:Dynamic, ?b:Dynamic):Null<Dynamic> {
		if (a is IHScriptAbstractBehaviour) {
			var ab:IHScriptAbstractBehaviour = cast a;
			if (ab.hasOp) return ab.hop(op, a, b);
		}
		// Also check right operand for symmetry
		if (b != null && b is IHScriptAbstractBehaviour) {
			var ab:IHScriptAbstractBehaviour = cast b;
			if (ab.hasOp) return ab.hop(op, a, b);
		}
		return null;
	}

	function tryArrayAccessGet(obj:Dynamic, key:Dynamic):Null<Dynamic> {
		if (obj is IHScriptAbstractBehaviour) {
			var ab:IHScriptAbstractBehaviour = cast obj;
			if (ab.hasArr) return ab.harrayget(key);
		}
		return null;
	}

	function tryArrayAccessSet(obj:Dynamic, key:Dynamic, val:Dynamic):Null<Dynamic> {
		if (obj is IHScriptAbstractBehaviour) {
			var ab:IHScriptAbstractBehaviour = cast obj;
			if (ab.hasArr) return ab.harrayset(key, val);
		}
		return null;
	}

	function tryResolve(obj:Dynamic, name:String):Null<Dynamic> {
		if (obj is IHScriptAbstractBehaviour) {
			var ab:IHScriptAbstractBehaviour = cast obj;
			if (ab.hasResolve) return ab.hresolve(name);
		}
		// also check for __resolve method
		try {
			var resolveFn = UnsafeReflect.field(obj, "__resolve");
			if (resolveFn != null && Reflect.isFunction(resolveFn)) {
				return resolveFn(name);
			}
		} catch(e:Dynamic) {}
		return null;
	}

	// @:from / @:to: applies stored conversion functions
	// For @:to: if val has a @:to conversion registered (instance method on a custom class,
	// or static method on a custom class via "using"), call it. Optionally restrict to a target type name.
	public static function tryConvertTo(val:Dynamic, ?targetType:String):Dynamic {
		if (val == null) return null;
		var list:Array<Dynamic> = UnsafeReflect.field(val, "__conversions_to");
		if (list == null) return null;
		for (entry in list) {
			if (targetType != null && entry.targetType != targetType) continue;
			try {
				if (Reflect.hasField(entry, "fn") && entry.fn != null && Reflect.isFunction(entry.fn)) {
					return entry.fn();
				} else if (Reflect.hasField(entry, "fieldName") && val is IHScriptCustomClassBehaviour) {
					var beh:IHScriptCustomClassBehaviour = cast val;
					var bound = beh.hget(entry.fieldName);
					if (bound != null && Reflect.isFunction(bound)) return Reflect.callMethod(val, bound, []);
				}
			} catch(e:Dynamic) {}
		}
		return null;
	}

	// For @:from: try to create an instance of targetType (a CustomClassHandler) from val,
	// using any static @:from function registered on it.
	public static function tryConvertFrom(targetType:Dynamic, val:Dynamic):Dynamic {
		if (targetType == null) return null;
		var list:Array<Dynamic> = UnsafeReflect.field(targetType, "__conversions_from");
		if (list == null) return null;
		for (entry in list) {
			try {
				var fn:Dynamic = entry.fn;
				if (fn != null && Reflect.isFunction(fn)) {
					var result = Reflect.callMethod(null, fn, [val]);
					if (result != null) return result;
				}
			} catch(e:Dynamic) {}
		}
		return null;
	}

	function tryCallable(obj:Dynamic, args:Array<Dynamic>):Null<Dynamic> {
		if (obj is IHScriptAbstractBehaviour) {
			var ab:IHScriptAbstractBehaviour = cast obj;
			if (ab.hasCall) return ab.hcall(args);
		}
		// also check for __call method
		try {
			var callFn = UnsafeReflect.field(obj, "__call");
			if (callFn != null && Reflect.isFunction(callFn)) {
				return UnsafeReflect.callMethodSafe(obj, callFn, args);
			}
		} catch(e:Dynamic) {}
		return null;
	}

	public inline function error(e:#if hscriptPos ErrorDef #else Error #end, rethrow = false):Dynamic {
		#if hscriptPos var e = new Error(e, curExpr.pmin, curExpr.pmax, curExpr.origin, curExpr.line); #end

		if(!rethrow) 
			throw e;
		else
			this.rethrow(e);
		
		return null;
	}

	public inline function warn(e:#if hscriptPos ErrorDef #else Error #end) {
		#if hscriptPos var e = new Error(e, curExpr.pmin, curExpr.pmax, curExpr.origin, curExpr.line); #end
		
		if(warnHandler != null)
			warnHandler(e);
		else
			trace('[ Warning ] ${Printer.errorToString(e)}');
	}

	inline function rethrow(e:Dynamic):Void {
		#if hl
		hl.Api.rethrow(e);
		#else
		throw e;
		#end
	}

	inline function getProperty(o:Null<Dynamic>, n:String, allowProperty:Bool = true):Dynamic {
		if(allowProperty && o != null && o is Property) {
			var prop:Property = cast o;
			return prop.get(isBypassAccessor);
		}
		else
			return o;
	}

	public function resolve(id:String, doException:Bool = true, allowProperty:Bool = true):Dynamic {
		if (id == null)
			return null;
		// StringTools.trim is O(1) on the leading/trailing whitespace and returns the original
		// reference when there is none, so it must NOT be pre-guarded by full-string scans.
		id = StringTools.trim(id);

		if(inCustomClass && id == 'super') {
			var customClass:IHScriptCustomClassBehaviour = cast scriptObject;
			var superClass = customClass.hget('superClass');
			return superClass == null ? customClass.hget('superConstructor') : superClass;
		}

		var l = locals.get(id);
		if(l != null) {
			return getProperty(l.r, id, allowProperty);
		}

		if(cacheValid) {
			var loc = varLocationCache.get(id);
			if(loc != null) {
				return switch(loc) {
					case VGlobal: getProperty(variables.get(id), id, allowProperty);
					case VPublic: getProperty(publicVariables.get(id), id, allowProperty);
					case VStatic: getProperty(staticVariables.get(id), id, allowProperty);
					case VScriptObject: isBypassAccessor ? UnsafeReflect.field(scriptObject, id) : UnsafeReflect.getProperty(scriptObject, id);
					case VScriptObjectGetter: UnsafeReflect.getProperty(scriptObject, 'get_$id')();
					case VCustomClass: (cast scriptObject:IHScriptCustomAccessBehaviour).hget(id);
					case VCustomClassBypass:
						var obj:IHScriptCustomAccessBehaviour = cast scriptObject;
						obj.__allowSetGet = false;
						var res = obj.hget(id);
						obj.__allowSetGet = true;
						res;
					case VBehaviourClass: (cast scriptObject:IHScriptCustomBehaviour).hget(id);
					case VAccessBehaviour: (cast scriptObject:IHScriptCustomAccessBehaviour).hget(id);
					case VAccessBehaviourBypass:
						var obj:IHScriptCustomAccessBehaviour = cast scriptObject;
						obj.__allowSetGet = false;
						var res = obj.hget(id);
						obj.__allowSetGet = true;
						res;
					case VNotFound:
						var cached = __typeResolveCache.get(id);
						if (cached != null) return cached;
						var cl = Type.resolveClass(id);
						if(cl != null) { __typeResolveCache.set(id, cl); return cl; }
						var en = Type.resolveEnum(id);
						if(en != null) { __typeResolveCache.set(id, en); return en; }
						if (doException) error(EUnknownVariable(id));
						null;
				}
			}
		}

		var v = variables.get(id);
		if (v != null) {
			varLocationCache.set(id, VGlobal);
			return getProperty(v, id, allowProperty);
		}
		if (variables.exists(id)) { // exists, but holds a null value
			varLocationCache.set(id, VGlobal);
			return null;
		}
		v = publicVariables.get(id);
		if (v != null) {
			varLocationCache.set(id, VPublic);
			return getProperty(v, id, allowProperty);
		}
		if (publicVariables.exists(id)) {
			varLocationCache.set(id, VPublic);
			return null;
		}
		v = staticVariables.get(id);
		if (v != null) {
			varLocationCache.set(id, VStatic);
			return getProperty(v, id, allowProperty);
		}
		if (staticVariables.exists(id)) {
			varLocationCache.set(id, VStatic);
			return null;
		}

		var cc = customClasses.get(id);
		if (cc != null)
			return cc;

		if (specialObject != null && specialObject.obj != null) {
			var specialObj = specialObject.obj;
			var exclusions = specialObject.exclusions;
			
			if (exclusions == null || !exclusions.contains(id)) {
				try {
					var val = UnsafeReflect.getProperty(specialObj, id);
					if (specialObject.includeFunctions == false && Reflect.isFunction(val)) {
						// Skip functions if includeFunctions is false
					} else {
						return val;
					}
				} catch (e:Dynamic) {
					// Property not accessible, continue to next check
				}
			}
		}

		if (hasScriptObject) {
			// search in object
			if (id == "this") {
				return scriptObject;
			}
			var instanceHasField = __instanceFields.exists(id);

			if (_scriptObjectType == SObject && instanceHasField) {
				varLocationCache.set(id, VScriptObject);
				return UnsafeReflect.field(scriptObject, id);
			} else if((_scriptObjectType == SCustomClass && instanceHasField) || _scriptObjectType == SAccessBehaviourObject) {
				var obj:IHScriptCustomAccessBehaviour = cast scriptObject;
				if(isBypassAccessor) {
					varLocationCache.set(id, VCustomClassBypass);
					obj.__allowSetGet = false;
					var res = obj.hget(id);
					obj.__allowSetGet = true;
					return res;
				}
				varLocationCache.set(id, VCustomClass);
				return obj.hget(id);
			} else if(_scriptObjectType == SBehaviourClass) {
				varLocationCache.set(id, VBehaviourClass);
				var obj:IHScriptCustomBehaviour = cast scriptObject;
				return obj.hget(id);
			}

			if (instanceHasField) {
				if(isBypassAccessor) {
					varLocationCache.set(id, VScriptObject);
					return UnsafeReflect.field(scriptObject, id);
				} else {
					varLocationCache.set(id, VScriptObject);
					return UnsafeReflect.getProperty(scriptObject, id);
				}
			} else if (__instanceFields.exists('get_$id')) { // getter
				return UnsafeReflect.getProperty(scriptObject, 'get_$id')();
			}
		}
		
		// @:resolve fallback
		if (hasScriptObject) {
			var r = tryResolve(scriptObject, id);
			if (r != null) return r;
		}

		varLocationCache.set(id, VNotFound);
		var cached = __typeResolveCache.get(id);
		if (cached != null) return cached;
		var cl = Type.resolveClass(id);
		if(cl != null) { __typeResolveCache.set(id, cl); return cl; }
		var en = Type.resolveEnum(id);
		if(en != null) { __typeResolveCache.set(id, en); return en; }
		if (doException)
			error(EUnknownVariable(id));
		return null;
	}

	public function invalidateCache():Void {
		varLocationCache.clear();
		__typeResolveCache.clear();
		cacheValid = true;
	}

	public static var importRedirects:Map<String, String> = new Map();
	public static function getImportRedirect(className:String):String {
		var redirect = importRedirects.get(className);
		return redirect != null ? redirect : className;
	}

	public var localImportRedirects:Map<String, String> = new Map();
	public function getLocalImportRedirect(className:String):String {
		var redirect = importRedirects.get(className);
		if (redirect != null)
			className = redirect;
		redirect = localImportRedirects.get(className);
		if (redirect != null)
			className = redirect;
		return className;
	}

	/** Handles `class Foo { ... }` declarations (extracted from the expr() switch). **/
	function exprClass(name:String, fields:Array<Expr>, extend:String, interfaces:Array<String>, isFinal:Bool):Void {
		// TODO: module isolation
		var oldName:String = name;
		var hasAlias:Bool = (setAlias != null && beforeAlias == oldName);
		var toSetName:String = hasAlias ? setAlias : oldName;

		if (customClasses.get(toSetName) != null) {
			warn(EAlreadyExistingClass(toSetName));
			return; // ignore it
		}

		inline function importVar(thing:String):String {
			if (thing == null)
				return null;
			final variable:Class<Any> = variables.exists(thing) ? cast variables.get(thing) : null;
			return variable == null ? thing : Type.getClassName(variable);
		}
		var cls:CustomClassHandler = new CustomClassHandler(this, oldName, fields, importVar(extend), [for (i in interfaces) importVar(i)], isFinal);
		customClasses.set(toSetName, cls);
		varLocationCache.remove(toSetName); // a previously-cached VNotFound must not shadow the newly registered class
		__typeResolveCache.remove(toSetName);
		if(hasAlias) {
			customClasses.set(oldName, cls); // Allow usage in the same module
			varLocationCache.remove(oldName);
			__typeResolveCache.remove(oldName);
			beforeAlias = null;
			setAlias = null;
		}
	}

	/** Handles `import` / `using` statements (extracted from the expr() switch). **/
	function exprImport(clsName:String, aliasAs:Null<String>, isUsing:Bool, isStar:Bool):Void {
		if(!importEnabled) return;

		if(isStar) {
			var realClassName = clsName;
			if(importBlocklist.contains(realClassName)) return;

			var cls = Type.resolveClass(realClassName);
			if(cls != null) {
				for(field in Reflect.fields(cls)) {
					if(!variables.exists(field)) {
						var t:Dynamic = Reflect.field(cls, field);
						if(t != null && (Type.getClass(t) != null || Type.getEnum(t) != null)) {
							variables.set(field, t);
						}
					}
				}
				var statics = Type.getClassFields(cls);
				for(f in statics) {
					if(!variables.exists(f)) {
						var t:Dynamic = Reflect.getProperty(cls, f);
						if(t != null && (Type.getClass(t) != null || Type.getEnum(t) != null)) {
							variables.set(f, t);
						}
					}
				}
			}
			return;
		}

		var splitClassName:Array<String> = [for (e in clsName.split(".")) e.trim()];
		var realClassName = splitClassName.join(".");
		var claVarName = splitClassName[splitClassName.length - 1];
		var toSetName = aliasAs != null ? aliasAs : claVarName;
		var oldClassName = realClassName;
		var oldSplitName = splitClassName.copy();

		if(variables.exists(toSetName)) { // class is already imported 
			if(isUsing && !usingHandler.entryExists(toSetName))
				setUsing(toSetName, variables.get(toSetName)); 

			return;
		}

		if(customClasses.get(toSetName) != null) { // custom class is already parsed and imported 
			// NOTE: you will need to create/import 
			// the custom class first before
			// setting the extension
			if(isUsing && !usingHandler.entryExists(toSetName))
				setCustomClassUsing(toSetName, customClasses.get(toSetName));

			return;
		}
		
		function importResolve(__clsName:String):Null<Dynamic> {
			var _realClassName = getLocalImportRedirect(__clsName);
			if(importBlocklist.contains(_realClassName)) {
				warn(ECustom('Invalid class: $_realClassName is blacklisted'));
				return null;
			}

			var _cl = Type.resolveClass(_realClassName);
			if(_cl == null) _cl = Type.resolveClass('${_realClassName}_HSC');
			return _cl;
		}

		var cl = importResolve(realClassName);
		var en = Type.resolveEnum(realClassName);
		//trace(realClassName, cl, en, splitClassName);

		// Allow for flixel.ui.FlxBar.FlxBarFillDirection;
		if(cl == null && en == null) {
			if(splitClassName.length > 1) {
				splitClassName.splice(-2, 1); // Remove the last last item
				realClassName = splitClassName.join(".");

				cl = importResolve(realClassName);
				en = Type.resolveEnum(realClassName);
				//trace(realClassName, cl, en, splitClassName);
			}
		}

		if(cl == null && en == null) {
			if(allowStaticImports) { //allows for static imports like "haxe.io.Path.normalize"
				var clPth:Array<String> = oldSplitName.copy();
				var funcName:String = clPth.pop();
				var statField:Dynamic = Reflect.getProperty(Type.resolveClass(StringTools.trim(clPth.join("."))), funcName);

				if(statField != null) {
					variables.set((toSetName != null && toSetName.length > 0 ? toSetName : funcName), statField);
					return;
				}
			}

			beforeAlias = claVarName;
			setAlias = aliasAs;
			if(importFailedCallback == null || !importFailedCallback(oldSplitName, toSetName)){
				beforeAlias = null;
				setAlias = null;
				error(EInvalidClass(oldClassName));
			}
		} else {
			//If the first letter of the alias is not an uppercase letter, then throw an error.
			//We don't need to worry about this for static imports.
			if(toSetName != claVarName && !Tools.isUppercase(toSetName)) {
				error(ECustom("Type aliases must start with an uppercase letter"));
				return;
			}

			if(en != null) { // ENUM!!!!
				if(isUsing) {
					error(EInvalidClass(oldClassName));
					return;
				}

				var enumThingy:HEnum = {};
				for(c in en.getConstructors()) {
					try {
						//UnsafeReflect.setField(enumThingy, c, en.createByName(c));
						enumThingy.setEnum(c, en.createByName(c));
					} catch(e) {
						try {
							//UnsafeReflect.setField(enumThingy, c, UnsafeReflect.field(en, c));
							enumThingy.setEnum(c, UnsafeReflect.field(en, c));
						} catch(ex) {
							throw e;
						}
					}
				}
				variables.set(toSetName, enumThingy);
			} else { //Standard class
				if(isUsing) setUsing(toSetName, cl);
				variables.set(toSetName, cl);
			}
		}
	}

	/** Handles `enum` declarations (extracted from the expr() switch). **/
	function exprEnum(en:EnumDecl, isAbstract:Bool):Void {
		if(isAbstract) {
			var enumObj:Dynamic = {};
			var enumType:String = 'Int';
			if(en.underlyingType != null) {
				enumType = switch(en.underlyingType) {
					case CTPath(path, _):
						path.join(".");
					default:
						''; // ???
				}
			}
			var enumName = en.name;
			var enumFields = en.fields;
			// Incremental implicit int value carried from the previous field:
			/*
			enum abstract Numeric(Int) {
				var Zero; // implicit value: 0
				var Ten = 10;
				var Eleven; // implicit value: 11
			}
			*/
			var lastValue:Dynamic = null;
			for (i => ef in enumFields) {
				var fieldName = ef.name;
				var fieldValue:Dynamic;
				if(ef.value != null) {
					fieldValue = expr(ef.value);
					if(enumType == 'Int' && Std.isOfType(fieldValue, Int))
						lastValue = fieldValue;
				} else {
					fieldValue = switch(enumType) {
						case 'Int':
							lastValue = lastValue != null ? Std.int(lastValue) + 1 : 0;
							lastValue;
						case 'String': fieldName;
						default: null;
					}
				}
				UnsafeReflect.setField(enumObj, fieldName, fieldValue);
			}
			if(en.functions != null) {
				for(fn in en.functions) expr(fn);
			}
			variables.set(enumName, enumObj);
		} else {
			var enumThingy:HEnum = {};
			var enumName = en.name;
			var enumFields = en.fields;
			for (i => ef in enumFields) {
				var fieldName = ef.name;
				
				if(ef.args.length < 1) {
					var enumValue:HEnumValue = {
						enumName: enumName,
						fieldName: fieldName,
						index: i,
						args: []
					}

					enumThingy.setEnum(fieldName, enumValue);
				}
				else {
					var params = ef.args;
					var hasOpt = false, minParams = 0;
					for (p in params) {
						if (p.opt)
							hasOpt = true;
						else
							minParams++;
					}
						
					var f = function(args:Array<Dynamic>):HEnumValue {
						if (((args == null) ? 0 : args.length) != params.length) {
							if (args.length < minParams) {
								var str = "Invalid number of parameters. Got " + args.length + ", required " + minParams;
								if (enumName != null)
									str += " for enum '" + enumName + "'";
								error(ECustom(str));
							}
							var args2 = [];
							var extraParams = args.length - minParams;
							var pos = 0;
							for (p in params)
								if (p.opt) {
									if (extraParams > 0) {
										args2.push(args[pos++]);
										extraParams--;
									} else
										args2.push(null);
								} else
									args2.push(args[pos++]);
							args = args2;
						}
						return {
							enumName: enumName,
							fieldName: fieldName,
							index: i,
							args: args
						};
					};
					var f = Reflect.makeVarArgs(f);

					enumThingy.setEnum(fieldName, f);
				}
			}

			variables.set(en.name, enumThingy);
		}
	}

	// TODO: separate large declarations (EClass, EEnum, etc...) into inline functions
	public function expr(e:Expr):Dynamic {
		#if hscriptPos
		curExpr = e;
		var e = e.e;
		#end
		switch (e) {
			case EPackage(_):
			case EClass(name, fields, extend, interfaces, isFinal):
				exprClass(name, fields, extend, interfaces, isFinal);
			case EImport(clsName, aliasAs, isUsing, isStar):
				exprImport(clsName, aliasAs, isUsing, isStar);
			case EEnum(en, isAbstract):
				exprEnum(en, isAbstract);
			case EInterface(name, fields, extend):
				var iface:Dynamic = {};
				for(f in fields) {
					var fe = Tools.expr(f);
					switch(fe) {
						case EVar(n, _, _, _, _, _, _, _, _, _, _):
							Reflect.setField(iface, n, null);
						case EFunction(_, _, fname, _):
							var fnObj = expr(f);
							if(fnObj != null && fname != null)
								Reflect.setField(iface, fname, fnObj);
						default:
							expr(f);
					}
				}
				variables.set(name, iface);
				return null;

			case ETypedef(name, t):
				switch(t) {
					case CTPath(path, _):
						var fullPath = path.join(".");
						var cl = Type.resolveClass(fullPath);
						if(cl != null) {
							variables.set(name, cl);
						} else {
							var en = Type.resolveEnum(fullPath);
							if(en != null) {
								var enumThingy:HEnum = {};
								for(c in en.getConstructors()) {
									try {
										enumThingy.setEnum(c, en.createByName(c));
									} catch(e) {
										try {
											enumThingy.setEnum(c, UnsafeReflect.field(en, c));
										} catch(ex) {
											throw e;
										}
									}
								}
								variables.set(name, enumThingy);
							}
						}
					default:
				}
				return null;
			case EAbstract(name, underlyingType, fields):
				var methods:Map<String, Dynamic> = new Map();
				var ctor:Dynamic = null;
				for(f in fields) {
					var fe = Tools.expr(f);
					switch(fe) {
						case EFunction(_, _, fname, _):
							var fnObj = expr(f);
							if(fname == "new") ctor = fnObj;
							else methods.set(fname, fnObj);
						default:
							expr(f);
					}
				}
				var absObj = {
					hnew: function(args:Array<Dynamic>):Dynamic {
						var instance:Dynamic = {};
						for(k in methods.keys())
							UnsafeReflect.setField(instance, k, methods.get(k));
						UnsafeReflect.setField(instance, "__value__", args.length > 0 ? args[0] : null);
						if(ctor != null) Reflect.callMethod(null, ctor, args);
						return instance;
					}
				};
				if(depth == 0) variables.set(name, absObj);
				else locals.set(name, {r: absObj, depth: depth, isFinal: false});
				return null;
			case ERegex(e, f):
				return new EReg(e, f);
			case EConst(c):
				return switch (c) {
					case CInt(v): v;
					case CFloat(f): f;
					case CString(s): s;
				}
			case EIdent(id):
				return resolve(id);
			case EVar(n, _, e, isPublic, isStatic, _, isFinal, _, getter, setter, isVar):
				var hasGetSet:Bool = (getter != null || setter != null);
				if(depth > 0 && hasGetSet) {
					error(ECustom("Property Accessor for local variables is not allowed"));
					return null;
				}
				declared.push({n: n, old: locals.get(n), depth: depth});
				var v:Dynamic = (e == null) ? null : expr(e);
				var r:Dynamic = null;
				if (hasGetSet) 
					r = new Property(n, v, getter, setter, isVar, isStatic, this);
				else
					r = v;
				var declVar:DeclaredVar = {
					r: r,
					depth: depth,
					isFinal: isFinal == true
				};
				locals.set(n, declVar);
				if (depth == 0 && blockDepth <= 1) {
					varLocationCache.remove(n);
					if(allowStaticVariables && isStatic == true) {
						if(!staticVariables.exists(n))
							staticVariables.set(n, locals[n].r);
						// live only in the shared map, so functions don't capture a stale
						// local copy and miss cross-script writes
						locals.remove(n);
					} else if(allowPublicVariables && isPublic == true) {
						if(!publicVariables.exists(n))
							publicVariables.set(n, locals[n].r);
						locals.remove(n);
					} else {
						variables.set(n, locals[n].r);
					}
				}
				return null;
			case EParent(e):
				return expr(e);
			case EBlock(exprs):
				var old:Int = declared.length;
				blockDepth++;
				var v:Null<Dynamic> = null;
				for (e in exprs)
					v = expr(e);
				blockDepth--;
				restore(old);
				return v;
			case EField(e, f, s):
				var field:Null<Dynamic>;
				try {
					field = expr(e);
				} catch(exc:Dynamic) {
					var path = getExprPath(e);
					if(path != null) {
						var fullPath = path + "." + f;
						var cl = Type.resolveClass(fullPath);
						if(cl != null) return cl;
						var en = Type.resolveEnum(fullPath);
						if(en != null) return en;
						if(s) return null;
						error(EUnknownVariable(path));
					}
					throw exc;
				}
				if(field == null) {
					var path = getExprPath(e);
					if(path != null) {
						var fullPath = path + "." + f;
						var cl = Type.resolveClass(fullPath);
						if(cl != null) return cl;
						var en = Type.resolveEnum(fullPath);
						if(en != null) return en;
					}
					if(s) return null;
				}
				return get(field, f);
			case EBinop(op, e1, e2):
				var opStr = op.toString();
				return switch(op) {
					case OpAdd, OpSub, OpMult, OpDiv, OpMod, OpAnd, OpOr, OpXor, OpShl, OpShr, OpUshr,
						 OpEq, OpNeq, OpGte, OpLte, OpGt, OpLt, OpInterval:
						var a:Dynamic = expr(e1);
						var b:Dynamic = expr(e2);
						var r = tryOpOverload(opStr, a, b);
						if (r != null) r
						else switch(op) {
							case OpAdd: (a is String || b is String) ? (Std.string(a) + Std.string(b)) : a + b;
							case OpSub: a - b;
							case OpMult: a * b;
							case OpDiv: a / b;
							case OpMod: a % b;
							case OpAnd: a & b;
							case OpOr: a | b;
							case OpXor: a ^ b;
							case OpShl: a << b;
							case OpShr: a >> b;
							case OpUshr: a >>> b;
							case OpEq: a == b;
							case OpNeq: a != b;
							case OpGte: a >= b;
							case OpLte: a <= b;
							case OpGt: a > b;
							case OpLt: a < b;
							case OpInterval: new IntIterator(a, b);
							default: error(EInvalidOp(opStr));
						}
					case OpBoolOr: expr(e1) == true || expr(e2) == true;
					case OpBoolAnd: expr(e1) == true && expr(e2) == true;
					case OpIs: checkIsType(e1, e2);
					case OpAssign: assign(e1, e2);
					case OpNcoal:
						var expr1:Dynamic = expr(e1);
						expr1 == null ? expr(e2) : expr1;
					case OpArrow: null;
					case OpAddAssign: evalAssignOp(OpAddAssign, function(v1:Dynamic, v2:Dynamic) return v1 + v2, e1, e2);
					case OpSubAssign: evalAssignOp(OpSubAssign, function(v1:Float, v2:Float) return v1 - v2, e1, e2);
					case OpMultAssign: evalAssignOp(OpMultAssign, function(v1:Float, v2:Float) return v1 * v2, e1, e2);
					case OpDivAssign: evalAssignOp(OpDivAssign, function(v1:Float, v2:Float) return v1 / v2, e1, e2);
					case OpModAssign: evalAssignOp(OpModAssign, function(v1:Float, v2:Float) return v1 % v2, e1, e2);
					case OpAndAssign: evalAssignOp(OpAndAssign, function(v1, v2) return v1 & v2, e1, e2);
					case OpOrAssign: evalAssignOp(OpOrAssign, function(v1, v2) return v1 | v2, e1, e2);
					case OpXorAssign: evalAssignOp(OpXorAssign, function(v1, v2) return v1 ^ v2, e1, e2);
					case OpShlAssign: evalAssignOp(OpShlAssign, function(v1, v2) return v1 << v2, e1, e2);
					case OpShrAssign: evalAssignOp(OpShrAssign, function(v1, v2) return v1 >> v2, e1, e2);
					case OpUshrAssign: evalAssignOp(OpUshrAssign, function(v1, v2) return v1 >>> v2, e1, e2);
					case OpNcoalAssign: evalAssignOp(OpNcoalAssign, function(v1, v2) return v1 == null ? v2 : v1, e1, e2);
					default: error(EInvalidOp(opStr));
				}
			case EUnop(op, prefix, e):
				var opStr = (prefix ? "" : "Post") + op.toString();
				var val:Dynamic = expr(e);
				var r = tryOpOverload(opStr, val);
				if (r != null) return r;
				switch (op) {
					case OpNot: return (val != true : Dynamic);
					case OpNeg: return -val;
					case OpIncrement: return increment(e, prefix, 1);
					case OpDecrement: return increment(e, prefix, -1);
					case OpNegBits: return ~val;
					default: error(EInvalidOp(opStr));
				}
			case ECall(e, params):
				var args:Array<Dynamic> = (params.length > 0) ? makeArgs(params) : _EMPTY_ARGS;

				switch (Tools.expr(e)) {
					case EField(e, f, s):
						var obj:Null<Dynamic> = expr(e);
						if (obj == null) {
							if(s) return null;
							error(EInvalidAccess(f));
						}
						return fcall(obj, f, args);
					default:
						var fn:Dynamic = expr(e);
						// @:callable support
						if (fn != null) {
							var r = tryCallable(fn, args);
							if (r != null) return r;
						}
						return call(null, fn, args);
				}
			case EIf(econd, e1, e2):
				return if (expr(econd) == true) expr(e1) else if (e2 == null) null else expr(e2);
			case EWhile(econd, e):
				whileLoop(econd, e);
				return null;
			case EDoWhile(econd, e):
				doWhileLoop(econd, e);
				return null;
			case EFor(v, it, e, ithv):
				forLoop(v, it, e, ithv);
				return null;
			case EBreak:
				throw SBreak;
			case EContinue:
				throw SContinue;
			case EReturn(e):
				returnValue = e == null ? null : expr(e);
				throw SReturn;
			case EFunction(params, fexpr, name, _, isPublic, isStatic, isOverride, isPrivate, isFinal, isInline):
				var capturedLocals:Map<String, DeclaredVar> = [];
				var hasCaptured:Bool = false;
				for (k => e in locals)
					if (e != null && e.depth > 0) {
						capturedLocals.set(k, e);
						hasCaptured = true;
					}

				var me = this;
				var hasOpt = false, minParams = 0;
				for (p in params)
					if (p.opt)
						hasOpt = true;
					else
						minParams++;
				var f = function(args:Array<Dynamic>) {
					if (me.locals == null || me.variables == null) return null;

					if (((args == null) ? 0 : args.length) != params.length) {
						if (args.length < minParams) {
							var str = "Invalid number of parameters. Got " + args.length + ", required " + minParams;
							if (name != null)
								str += " for function '" + name + "'";
							error(ECustom(str));
						}
						// make sure mandatory args are forced
						var args2 = [];
						var extraParams = args.length - minParams;
						var pos = 0;
						for (p in params)
							if (p.opt) {
								if (extraParams > 0) {
									args2.push(args[pos++]);
									extraParams--;
								} else
									args2.push(null);
							} else
								args2.push(args[pos++]);
						args = args2;
					}
					var old = me.locals, depth = me.depth;
					me.depth++;
					me.locals = hasCaptured ? me.duplicate(capturedLocals) : new Map();
					for (i in 0...params.length)
						me.locals.set(params[i].name, {r: args[i], depth: depth, isFinal: false});
					var r:Null<Dynamic> = null;
					var oldDecl:Int = declared.length;
					if (inTry)
						try {
							r = me.exprReturn(fexpr);
						} catch (e:Dynamic) {
							me.locals = old;
							me.depth = depth;
							#if neko
							neko.Lib.rethrow(e);
							#else
							throw e;
							#end
						}
					else
						r = me.exprReturn(fexpr);
					restore(oldDecl);
					me.locals = old;
					me.depth = depth;
					return r;
				};
				var f = Reflect.makeVarArgs(f);
				if (name != null) {
					if (depth == 0) {
						// global function
						if(isStatic && allowStaticVariables) {
							staticVariables.set(name, f);
						} else if(isPublic && allowPublicVariables) {
							publicVariables.set(name, f);
						} else {
							variables.set(name, f);
						}
					} else {
						// function-in-function is a local function
						declared.push({n: name, old: locals.get(name), depth: depth});
						var ref:DeclaredVar = {r: f, depth: depth, isFinal: false};
						locals.set(name, ref);
						capturedLocals.set(name, ref); // allow self-recursion
					}
				}
				return f;
			case EArrayDecl(arr, wantedType):
				var isMap:Bool = false;

				if (wantedType != null) {
					isMap = switch (wantedType) {
						case CTPath(["Map"], [_, _]): true;
						case CTPath(["StringMap"], [_]): true;
						case CTPath(["IntMap"], [_]): true;
						case CTPath(["ObjectMap"], [_]): true;
						case CTPath(["EnumMap"], [_]): true;
						default: false;
					};
				}

				if (!isMap && arr.length > 0) {
					isMap = Tools.expr(arr[0]).match(EBinop(OpArrowFn, _));
				}

				// TODO: separate this into a function
				if (isMap) {
					var isAllString:Bool = true;
					var isAllInt:Bool = true;
					var isAllObject:Bool = true;
					var isAllEnum:Bool = true;
					var keys:Array<Dynamic> = [];
					var values:Array<Dynamic> = [];

					for (e in arr) {
						switch (Tools.expr(e)) {
							case EBinop(OpArrowFn, eKey, eValue):
								var key:Dynamic = expr(eKey);
								var value:Dynamic = expr(eValue);
								isAllString = isAllString && (key is String);
								isAllInt = isAllInt && (key is Int);
								isAllObject = isAllObject && Reflect.isObject(key);
								isAllEnum = isAllEnum && Reflect.isEnumValue(key);
								keys.push(key);
								values.push(value);
							default:
								throw "=> expected";
						}
					}

					if (wantedType != null) {
						isAllString = isAllString && (
							wantedType.match(CTPath(["Map"], [CTPath(["String"], _), _])) || wantedType.match(CTPath(["StringMap"], [_]))
						);
						isAllInt = isAllInt && (
							wantedType.match(CTPath(["Map"], [CTPath(["Int"], _), _])) || wantedType.match(CTPath(["IntMap"], [_]))
						);
						isAllObject = isAllObject && (
							wantedType.match(CTPath(["Map"], [CTPath(["Dynamic"], _), _])) || wantedType.match(CTPath(["ObjectMap"], [_, _]))
						);
						isAllEnum = isAllEnum && (
							wantedType.match(CTPath(["Map"], [CTPath(["Enum"], _), _])) || wantedType.match(CTPath(["EnumMap"], [_, _]))
						);

						if (!isAllString && !isAllInt && !isAllObject && !isAllEnum) {
							isAllObject = true; // Assume dynamic
							//throw "Unknown Type Key";
						}
					}

					var map:Dynamic = {
						if (isAllInt)
							new haxe.ds.IntMap<Dynamic>();
						else if (isAllString)
							new haxe.ds.StringMap<Dynamic>();
						else if (isAllEnum)
							new haxe.ds.EnumValueMap<Dynamic, Dynamic>();
						else if (isAllObject)
							new haxe.ds.ObjectMap<Dynamic, Dynamic>();
						else
							throw 'Unknown Type Key';
					}
					for (n in 0...keys.length) {
						setMapValue(getMap(map), keys[n], values[n]);
					}
					return map;
				} else {
					var a = [];
					for (e in arr) {
						a.push(expr(e));
					}
					return a;
				}
			case EArray(e, index):
				var arr:Dynamic = expr(e);
				var index:Dynamic = expr(index);
				var r = tryArrayAccessGet(arr, index);
				if (r != null) return r;
				if (isMap(arr)) {
					return getMapValue(getMap(arr), index);
				} else {
					return arr[index];
				}
			case ENew(cl, params, _):
				var a:Array<Dynamic> = (params.length > 0) ? makeArgs(params) : _EMPTY_ARGS;
				return cnew(cl, a);
			case EThrow(e):
				throw expr(e);
			case ETry(e, catches):
				var old:Int = declared.length;
				var oldTry = inTry;
				try {
					inTry = true;
					var v:Dynamic = expr(e);
					restore(old);
					inTry = oldTry;
					return v;
				} catch (err:Stop) {
					inTry = oldTry;
					throw err;
				} catch (err:Dynamic) {
					restore(old);
					inTry = oldTry;
					for(c in catches) {
						if(c.t != null) {
							var typeName = switch(c.t) {
								case CTPath(path, _): path.join(".");
								default: null;
							}
							var catchType = typeName != null ? Type.resolveClass(typeName) : null;
							if(catchType != null && !Std.isOfType(err, catchType))
								continue;
						}
						declared.push({n: c.v, old: locals.get(c.v), depth: depth});
						locals.set(c.v, {r: err, depth: depth, isFinal: false});
						var v:Dynamic = expr(c.expr);
						restore(old);
						return v;
					}
					throw err;
				}
			case EObject(fl):
				var o = {};
				for (f in fl)
					UnsafeReflect.setField(o, f.name, expr(f.e));
				return o;
			case ETernary(econd, e1, e2):
				return if (expr(econd) == true) expr(e1) else expr(e2);
			case ESwitch(e, cases, def):
				var old:Int = declared.length;
				var val:Dynamic = expr(e);
				var match = false;
				for (c in cases) {
					var caseOld = declared.length;
					for (v in c.values) {
						// https://github.com/FunkinCrew/polymod/blob/5d47a5c7c6b4e0cb94bd8fd45d012ca93bde9ab7/polymod/hscript/_internal/Interp.hx#L613
						switch (Tools.expr(v)) {
							case ECall(e, params):
								switch (Tools.expr(e)) {
									case EField(_, f):
										var isScripted:Bool = val is HEnumValue;
										var valStr:String = '';
										var valEnum:HEnumValue = null;
										if(isScripted)  {
											valEnum = cast val;
											valStr = valEnum.fieldName;
										}
										else {
											valStr = cast val;
											valStr = valStr.substring(0, valStr.indexOf("("));
										}

										if(valStr == f) {
											var valParams = isScripted ? valEnum.getConstructorArgs() : Type.enumParameters(val);
											for (i => p in params) {
												switch (Tools.expr(p)) {
													case EIdent(n):
														declared.push({
															n: n,
															old: locals.get(n),
															depth: depth
														});
														locals.set(n, {r: valParams[i], depth: depth, isFinal: false});
													default:
												}
											}
											match = true;
											break;
										}
									default:
								}
							case EArrayDecl(elements):
								if (val is Array) {
									match = matchArrayPattern(cast val, elements);
								}
								if (match) break;
							case EObject(fields):
								if (val is Dynamic && !(val is Array) && !(val is String) && !(val is Bool) && !(val is Int) && !(val is Float)) {
									match = matchObjectPattern(val, fields);
								}
								if (match) break;
							case EIdent("_"):
								match = true;
								break;
							case EIdent(n):
								declared.push({n: n, old: locals.get(n), depth: depth});
								locals.set(n, {r: val, depth: depth, isFinal: false});
								match = true;
								break;
							case EBinop(OpOr, _, _):
								match = matchOrPattern(v, val);
								break;
							default:
								if (expr(v) == val) {
									match = true;
									break;
								}
						}
					}
					
					if (match) {
						if(c.guard != null) {
							if(!expr(c.guard)) {
								match = false;
								restore(caseOld);
							}
						}
					}
					if (match) {
						val = expr(c.expr);
						break;
					}
				}
				if (!match)
					val = def == null ? null : expr(def);
				restore(old);
				return val;
			case EMeta(a, b, e):
				var oldAccessor = isBypassAccessor;
				if(a == ":bypassAccessor") {
					isBypassAccessor = true;
				}
				var metaName = (a.charCodeAt(0) == ':'.code) ? a.substr(1) : a;
				var val = expr(e);
				if(UnsafeReflect.isObject(val)) {
					try {
						var metas:Array<Dynamic> = UnsafeReflect.field(val, "__metas");
						if(metas == null) {
							metas = [];
							UnsafeReflect.setField(val, "__metas", metas);
						}
						var metaParams:Array<Dynamic> = null;
						if(b != null) {
							metaParams = [];
							for(p in b) metaParams.push(expr(p));
						}
						metas.push({ name: metaName, params: metaParams });
					} catch(e:Dynamic) {}
				}
				isBypassAccessor = oldAccessor;
				return val;
			case ECheckType(e, _):
				return expr(e);
			case ECast(e, t):
				var val = expr(e);
				if (t != null) {
					var targetType = new Printer().typeToString(t);
					var converted = tryConvertTo(val, targetType);
					if (converted != null) return converted;
					if (customClasses.exists(targetType)) {
						var converted2 = tryConvertFrom(customClasses.get(targetType), val);
						if (converted2 != null) return converted2;
					}
				}
				return val;
		}
		return null;
	}

	inline function doWhileLoop(econd:Expr, e:Expr):Void {
		var old = declared.length;
		do {
			if (!loopBody(e))
				break;
		} while (expr(econd) == true);
		restore(old);
	}

	inline function whileLoop(econd:Expr, e:Expr):Void {
		var old = declared.length;
		while (expr(econd) == true) {
			if (!loopBody(e))
				break;
		}
		restore(old);
	}

	/** Attempts to write `value` to the cached location of `id`. Returns false if there is no usable cached location (caller falls back to the slow path). **/
	function cachedSet(id:String, value:Dynamic):Bool {
		if (!cacheValid) return false;
		var loc = varLocationCache.get(id);
		if (loc == null) return false;
		switch (loc) {
			case VGlobal:
				var cur = variables.get(id);
				if (cur is Property) (cast cur:Property).set(value, isBypassAccessor);
				else variables.set(id, value);
			case VPublic:
				var cur = publicVariables.get(id);
				if (cur is Property) (cast cur:Property).set(value, isBypassAccessor);
				else publicVariables.set(id, value);
			case VStatic:
				var cur = staticVariables.get(id);
				if (cur is Property) (cast cur:Property).set(value, isBypassAccessor);
				else staticVariables.set(id, value);
			case VScriptObject:
				if (_scriptObjectType == SObject || isBypassAccessor)
					UnsafeReflect.setField(scriptObject, id, value);
				else
					UnsafeReflect.setProperty(scriptObject, id, value);
			case VCustomClassBypass:
				var obj:IHScriptCustomAccessBehaviour = cast scriptObject;
				obj.__allowSetGet = false;
				obj.hset(id, value);
				obj.__allowSetGet = true;
			case VCustomClass:
				(cast scriptObject:IHScriptCustomAccessBehaviour).hset(id, value);
			case VAccessBehaviourBypass:
				var obj:IHScriptCustomAccessBehaviour = cast scriptObject;
				obj.__allowSetGet = false;
				obj.hset(id, value);
				obj.__allowSetGet = true;
			case VAccessBehaviour:
				(cast scriptObject:IHScriptCustomAccessBehaviour).hset(id, value);
			case VBehaviourClass:
				(cast scriptObject:IHScriptCustomBehaviour).hset(id, value);
			case VScriptObjectGetter, VNotFound:
				return false;
		}
		return true;
	}

	inline function makeIterator(v:Dynamic, ?allowKeyValue = false):Iterator<Dynamic> {
		#if js
		// don't use try/catch (very slow)
		if(v is Array) {
			return allowKeyValue ? (v:Array<Dynamic>).keyValueIterator() : (v:Array<Dynamic>).iterator();
		}
		if(allowKeyValue && v.keyValueIterator != null)
			v = v.keyValueIterator();
		else if (v.iterator != null)
			v = v.iterator();
		#elseif cpp
		if (v is Array) {
			return allowKeyValue ? (v:Array<Dynamic>).keyValueIterator() : (v:Array<Dynamic>).iterator();
		}
		if (allowKeyValue) {
			try v = v.keyValueIterator() catch (e:Dynamic) {};
		}
		if (v.hasNext == null || v.next == null) {
			try v = v.iterator() catch (e:Dynamic) {};
		}
		#else
		if(allowKeyValue) 
			try v = v.keyValueIterator() catch (e:Dynamic) {};

		if(v.hasNext == null || v.next == null) 
			try v = v.iterator() catch (e:Dynamic) {};
		
		#end
		if (v.hasNext == null || v.next == null) error(EInvalidIterator(v));
		return v;
	}

	inline function makeArgs(params:Array<Expr>):Array<Dynamic> {
		var args:Array<Dynamic> = [];
		#if cpp
		untyped __cpp__('{0}->reserve({1}->length)', args, params);
		#end
		for (p in params) {
			switch (Tools.expr(p)) {
				case EIdent(id):
					var ident:Dynamic = resolve(id);
					if (ident is CustomClass) {
						var customClass:CustomClass = cast ident; // Pass the underlying superclass if exist
						args.push(customClass.__superClass != null ? customClass.getSuperclass() : customClass);
					} else {
						args.push(ident);
					}
				default:
					args.push(expr(p));
			}
		}

		return args;
	}

	inline function forLoop(n:String, it:Expr, e:Expr, ?ithv:String):Void {
		var isKeyValue = ithv != null;
		var old = declared.length;
		if(isKeyValue)
			declared.push({n: ithv, old: locals.get(ithv), depth: depth});
		declared.push({n: n, old: locals.get(n), depth: depth});
		var it = makeIterator(expr(it), isKeyValue);
		var _hasNext = it.hasNext;
		var _next = it.next;
		while (_hasNext()) {
			var next = _next();
			if(isKeyValue)
				locals.set(ithv, {r: next.key, depth: depth, isFinal: false});
			locals.set(n, {r: isKeyValue ? next.value : next, depth: depth, isFinal: false});
			if (!loopBody(e))
				break;
		}
		restore(old);
	}

	/** Evaluates a loop body, handling SContinue/SBreak/SReturn without allocating a closure per iteration. **/
	function loopBody(e:Expr):Bool {
		try {
			expr(e);
		} catch (err:Stop) {
			switch (err) {
				case SContinue:
				case SBreak:
					return false;
				case SReturn:
					throw err;
			}
		}
		return true;
	}

	inline function isMap(o:Dynamic):Bool {
		return (o is IMap);
	}

	inline function getMap(map:Dynamic):IMap<Dynamic, Dynamic> {
		return cast map;
	}

	inline function getMapValue(map:IMap<Dynamic, Dynamic>, key:Dynamic):Dynamic {
		return map.get(key);
	}

	inline function setMapValue(map:IMap<Dynamic, Dynamic>, key:Dynamic, value:Dynamic):Void {
		map.set(key, value);
	}

	public static var getRedirects:Map<String, Dynamic->String->Dynamic> = [];
	public static var setRedirects:Map<String, Dynamic->String->Dynamic->Dynamic> = [];

	private static var _getRedirect:Dynamic->String->Dynamic;
	private static var _setRedirect:Dynamic->String->Dynamic->Dynamic;

	public var useRedirects:Bool = false;

	static function getClassType(o:Dynamic, ?cls:Class<Any>):Null<String> {
		return switch (Type.typeof(o)) {
			case TNull: "Null";
			case TInt: "Int";
			case TFloat: "Float";
			case TBool: "Bool";
			case _:
				if (cls == null)
					cls = Type.getClass(o);
				cls != null ? Type.getClassName(cls) : null;
		};
	}

	function getExprPath(e:Expr):Null<String> {
		switch(Tools.expr(e)) {
			case EIdent(id):
				return id;
			case EField(e2, f, _):
				var parent = getExprPath(e2);
				if(parent != null)
					return parent + "." + f;
				return null;
			default:
				return null;
		}
	}

	function get(o:Dynamic, f:String):Dynamic {
		if (o == null)
			error(EInvalidAccess(f));

		// @:deprecated warning
		try {
			var fieldMetas:Array<Dynamic> = cast UnsafeReflect.field(o, "__metas_" + f);
			if (fieldMetas != null) {
				for (m in fieldMetas) {
					if (m.name == "deprecated") {
						var msg = m.params != null && m.params.length > 0 ? m.params[0] : "";
						warn(ECustom('Field "$f" is deprecated${msg != "" ? ": " + msg : ""}'));
					}
				}
			}
		} catch(e:Dynamic) {}

		var cls:Null<Class<Dynamic>> = useRedirects ? Type.getClass(o) : null;
		if (useRedirects && {
			var cl:Null<String> = getClassType(o, cls);
			cl != null && getRedirects.exists(cl) && (_getRedirect = getRedirects[cl]) != null;
		}) {
			return _getRedirect(o, f);
		}
		
		if (o is IHScriptCustomAccessBehaviour) {
			var obj:IHScriptCustomAccessBehaviour = cast o;
			if(isBypassAccessor) {
				obj.__allowSetGet = false;
				var res = obj.hget(f);
				obj.__allowSetGet = true;
				return res;
			}
			return obj.hget(f);
		}

		if (o is IHScriptCustomBehaviour) {
			var obj:IHScriptCustomBehaviour = cast o;
			return obj.hget(f);
		}
		var v:Null<Dynamic> = null;
		if(isBypassAccessor) {
			#if cpp
			v = untyped __cpp__('{0}->__Field({1}, ::hx::paccNever)', o, f);
			if (v == null && useRedirects)
				v = Reflect.field(cls, f);
			#else
			if ((v = UnsafeReflect.field(o, f)) == null && useRedirects)
				v = Reflect.field(cls, f);
			#end
		}

		if(v == null) {
			#if php
			// https://github.com/HaxeFoundation/haxe/issues/4915
			try {
				if ((v = UnsafeReflect.getProperty(o, f)) == null && useRedirects)
					v = Reflect.getProperty(cls, f);
			}
			catch(e:Dynamic) {
				if ((v = UnsafeReflect.field(o, f)) == null && useRedirects)
					v = Reflect.field(cls, f);
			}
			#else
			if ((v = UnsafeReflect.getProperty(o, f)) == null && useRedirects)
				v = Reflect.getProperty(cls, f);
			#end
		}

		// @:resolve fallback: try resolve if still null
		if (v == null) {
			v = tryResolve(o, f);
		}

		return v;
	}

	function set(o:Dynamic, f:String, v:Dynamic):Dynamic {
		if (o == null)
			error(EInvalidAccess(f));

		// @:const check
		try {
			var fieldMetas:Array<Dynamic> = cast UnsafeReflect.field(o, "__metas_" + f);
			if (fieldMetas != null) {
				for (m in fieldMetas) {
					if (m.name == "const" || m.name == ":const") {
						error(ECustom('Cannot modify constant field "$f"'));
					}
				}
			}
		} catch(e:Dynamic) {}
		// also check @:const on object's global metas
		var metas:Array<Dynamic> = getMetas(o);
		if (metas != null) {
			var fmeta = getMeta(o, "const_" + f);
			if (fmeta != null) error(ECustom('Cannot modify constant field "$f"'));
		}

		if (useRedirects && {
			var cl:Null<String> = getClassType(o);
			cl != null && setRedirects.exists(cl) && (_setRedirect = setRedirects[cl]) != null;
		})
			return _setRedirect(o, f, v);
		
		if (o is IHScriptCustomAccessBehaviour) {
			var obj:IHScriptCustomAccessBehaviour = cast o;
			if(isBypassAccessor) {
				obj.__allowSetGet = false;
				var res = obj.hset(f, v);
				obj.__allowSetGet = true;
				return res;
			}
			return obj.hset(f, v);
		}

		if (o is IHScriptCustomBehaviour) {
			var obj:IHScriptCustomBehaviour = cast o;
			return obj.hset(f, v);
		}

		// Can use unsafe reflect here, since we checked for null above
		#if cpp
		if(isBypassAccessor) {
			untyped __cpp__('{0}->__SetField({1}, {2}, ::hx::paccNever)', o, f, v);
		} else {
			untyped __cpp__('{0}->__SetField({1}, {2}, ::hx::paccAlways)', o, f, v);
		}
		#else
		if(isBypassAccessor) {
			UnsafeReflect.setField(o, f, v);
		} else {
			UnsafeReflect.setProperty(o, f, v);
		}
		#end
		return v;
	}

	// STATIC EXTENSION ("USING")

	// Real class static extension
	function setUsing(name:String, obj:Dynamic) {
		if (usingHandler.entryExists(name)) return;
		if (UsingHandler.defaultExtension.exists(name)) {
			var us:UsingEntry = UsingHandler.defaultExtension.get(name);
			usingHandler.usingEntries.set(name, us);
			usingHandler.hasUsingEntries = true;
			return;
		}
		if (obj == null) error(ECustom("Unknown using class " + name));

		var fn:Dynamic->String->Array<Dynamic>->Dynamic = null;
		var fields:Array<String> = [];
		var cls = obj;

		switch (Type.typeof(cls)) {
			case TClass(c):
				fields = Type.getClassFields(c);
			case TObject:
				fields = Reflect.fields(cls);
			default:
				error(ECustom('$name is not a class'));
		}

		fn = function(o:Dynamic, f:String, args:Array<Dynamic>) {
			var field = Reflect.field(cls, f);
			if (field == null || !Reflect.isFunction(field))
				return null;

			// invalid if the function has no arguments
			var totalArgs = Tools.argCount(field);
			if (totalArgs == 0)
				return null;

			return UnsafeReflect.callMethodUnsafe(cls, field, [o].concat(args));
		}

		if(fn != null) usingHandler.registerEntry(name, fn, fields);
	}

	// Custom Class Static Extension
	@:access(hscript.CustomClassHandler)
	function setCustomClassUsing(name:String, cls:CustomClassHandler) {
		if (usingHandler.entryExists(name)) return;

		var fn:Dynamic->String->Array<Dynamic> -> Dynamic;
		var customClass:CustomClassHandler = cls;
		var fields:Array<String> = customClass.__staticFields.copy();

		fn = function(o:Dynamic, f:String, args:Array<Dynamic>):Dynamic {
			if (customClass.isNoUsing(f))
				return null;
			var field:Dynamic = customClass.getField(f);
			if (field == null || !Reflect.isFunction(field))
				return null;
			/*
			var totalArgs:Int = Tools.argCount(field);
			if (totalArgs == 0)
				return null;
			 */
			return UnsafeReflect.callMethodUnsafe(null, field, [o].concat(args));
		}

		usingHandler.registerEntry(name, fn, fields);
	}

	function fcall(o:Dynamic, f:String, args:Array<Dynamic>):Dynamic {
		// Custom logic to handle super calls to prevent infinite recursion
		if(inCustomClass) {
			var superCls:Dynamic = scriptObject.__superClass;
			if (o == superCls) {
				if (superCls is CustomClass)
					return cast(superCls, CustomClass).call(f, args, true);
				else
					return UnsafeReflect.callMethodUnsafe(superCls, UnsafeReflect.field(superCls, '_HX_SUPER__$f'), args);
			}
			if (superCls is CustomClass) {
				superCls = cast(superCls, CustomClass).__superClass;
				while (superCls != null) {
					if (o == superCls) {
						if (superCls is CustomClass)
							return cast(superCls, CustomClass).call(f, args, true);
						else
							return UnsafeReflect.callMethodUnsafe(superCls, UnsafeReflect.field(superCls, '_HX_SUPER__$f'), args);
					}
					superCls = (superCls is CustomClass) ? cast(superCls, CustomClass).__superClass : null;
				}
			}
		}

		if (usingHandler.hasUsingEntries) { // If is not empty
			var v:Dynamic = null;
			var clsName:String = o is CustomClassHandler ? cast(o, CustomClassHandler).name : Type.getClassName(Type.getClass(o));
			// TODO: optimize this
			if(!usingHandler.entryExists(clsName)) {
				for (n => us in usingHandler.usingEntries) {
					if (us.hasField(f)) {
						v = us.call(o, f, args);
						if (v != null)
							return v;
					}
				}
			}
			
		}

		var func = get(o, f);
		// Workaround for an HTML5-specific issue.
		// https://github.com/HaxeFoundation/haxe/issues/11298
		#if js
		if (func == null && f == "contains") {
			func = get(o, "includes");
		}
		#end

		return call(o, func, args);
	}

	inline function call(o:Dynamic, f:Dynamic, args:Array<Dynamic>):Dynamic {
		return UnsafeReflect.callMethodSafe(o, f, args);
	}

	function cnew(cl:String, args:Array<Dynamic>):Dynamic {
		var c:Dynamic = Type.resolveClass(cl);
		if (c == null)
			c = resolve(cl);
		if (c is IHScriptCustomConstructor)
			return cast(c, IHScriptCustomConstructor).hnew(args);
		if(UnsafeReflect.isObject(c) && Reflect.isFunction(c.hnew))
			return c.hnew(args);
		// @:structInit: if class has this metadata and single arg is an object,
		// create instance then copy fields from the object
		if (args.length == 1 && UnsafeReflect.isObject(args[0])) {
			try {
				var metas:Array<Dynamic> = cast UnsafeReflect.field(c, "__metas");
				if (metas != null) {
					for (m in metas) {
						if (m.name == "structInit" || m.name == ":structInit") {
							var instance = Type.createEmptyInstance(c);
							for (f in Reflect.fields(args[0]))
								UnsafeReflect.setField(instance, f, Reflect.field(args[0], f));
							return instance;
						}
					}
				}
			} catch(e:Dynamic) {}
		}
		return Type.createInstance(c, args);
	}
}