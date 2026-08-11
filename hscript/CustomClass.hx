package hscript;

import hscript.utils.UnsafeReflect;
import haxe.Constraints.Function;

using Lambda;

/**
 * The Custom Class core.
 * 
 * Provides handlers for custom classes.
 * 
 * @author Jamextreme140
 */
@:access(hscript.CustomClassHandler)
class CustomClass implements IHScriptCustomClassBehaviour {
	public var className(get, never):String;

	private function get_className():String
		return __class.name;

	public var __interp:Interp;
	public var __real_fields:Array<String> = []; // UNUSED
	public var __class__fields:Array<String> = []; // Declared fields

	public var __allowSetGet:Bool = true;

	var __class:CustomClassHandler;
	var __superClass:IHScriptCustomClassBehaviour;
	var __upperClass:IHScriptCustomClassBehaviour;
	var __constructor:Function;

	var __overrideFields:Array<String> = [];
	var __cachedFieldSet:Map<String, Dynamic> = null;
	var initializing:Bool = false;

	public function new(__class:CustomClassHandler, ?args:Array<Dynamic>, ?cachedFieldSet:Map<String, Dynamic>) {
		this.__class = __class;

		__interp = new Interp();
		__interp.errorHandler = __class.__interp.errorHandler;
		__interp.importFailedCallback = __class.__interp.importFailedCallback;

		// __interp.variables = __class.staticInterp.variables;
		@:privateAccess __interp.usingHandler.usingEntries = __class.ogInterp.usingHandler.usingEntries;
		__interp.publicVariables = __class.ogInterp.publicVariables;
		__interp.staticVariables = __class.ogInterp.staticVariables;
		__interp.customClasses = __class.ogInterp.customClasses;

		// Allow Parent Access on Classes
		if (__class.ogInterp.specialObject != null && __class.ogInterp.specialObject.obj != null) {
			__interp.specialObject = __class.ogInterp.specialObject;
		} else if (__class.ogInterp.scriptObject != null && !(__class.ogInterp.scriptObject is CustomClass)) {
			__interp.specialObject = {obj: __class.ogInterp.scriptObject, includeFunctions: true, exclusions: []};
		}

		// Allow Public and Static Variables
		__interp.allowStaticVariables = true;
		__interp.allowPublicVariables = true;

		for(f => v in __class.__interp.variables) {
			if(f == 'new') continue;
			if (!__interp.variables.exists(f))
				__interp.variables.set(f, v);
		}

		for (f in __class.fields) {
			var fieldMetas:Array<Dynamic> = null;
			var fieldExpr = Tools.expr(f);
			// Unwrap EMeta to extract per-field metadata
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
				case EVar(n): {
					__class__fields.push(n);
					if (fieldMetas != null)
						UnsafeReflect.setField(this, "__metas_" + n, fieldMetas);
				}
				case EFunction(_, _, n, ret, _, _, isOverride): {
					if(isOverride) __overrideFields.push(n);
					__class__fields.push(n);
					if (fieldMetas != null) {
						UnsafeReflect.setField(this, "__metas_" + n, fieldMetas);
						for (m in fieldMetas) {
							if ((m.name == "to" || m.name == ":to") && ret != null) {
								var targetType = new Printer().typeToString(ret);
								var list:Array<Dynamic> = UnsafeReflect.field(this, "__conversions_to");
								if (list == null) {
									list = [];
									UnsafeReflect.setField(this, "__conversions_to", list);
								}
								// fn is resolved lazily via hget so it always reflects the bound instance method
								list.push({ targetType: targetType, fieldName: n });
							}
						}
					}
				}
				default: continue;
			}
			@:privateAccess __interp.exprReturn(f);
		}

		__interp.scriptObject = this;

		initializing = true;

		if(cachedFieldSet != null)
			for(f => v in cachedFieldSet)
				this.hset(f, v);

		if (hasField('new')) {
			buildConstructor();
			call('new', args);

			if(__cachedFieldSet != null) {
				__cachedFieldSet.clear();
				__cachedFieldSet = null;
			}

			if (this.__superClass == null && __class.extend != null)
				__interp.error(ECustom("super() not called"));
		} else if (__class.extend != null) {
			buildSuperClass(args);
		}

		initializing = false;
	}

	function cacheFieldSet(name:String, val:Dynamic) {
		if(!initializing) return;
		if(__cachedFieldSet == null) __cachedFieldSet = [];
		__cachedFieldSet.set(name, val);
	}

	function buildConstructor() {
		__constructor = Reflect.makeVarArgs(buildSuperClass);
	}

	function buildSuperClass(?args:Array<Dynamic>) {
		if (args == null)
			args = [];

		if (__class.cl == null) {
			__interp.error(ECustom('Current class does not have a super'));
			return;
		}

		if (__class.cl is CustomClassHandler) {
			var customClass = new CustomClass(__class.cl, args, __cachedFieldSet);
			if(__overrideFields.length > 0) {
				for (field in __overrideFields) {
					var func = __interp.variables.get(field);
					customClass.overrideField(field, func);
				}
			}
			customClass.__upperClass = this;
			__superClass = customClass;
			@:privateAccess __interp.__instanceFields = __interp.__instanceFields.concat(getSuperFields());
		} else {
			if(__cachedFieldSet != null)
				UnsafeReflect.setField(__class.cl, "__cachedFieldSet", __cachedFieldSet);

			__superClass = Type.createInstance(__class.cl, args);
			var disallowCopy:Array<String> = {
				var fieldMap:Map<String, String> = []; // Prevent duplicate values
				for(f in Reflect.fields(__superClass).concat(Type.getInstanceFields(Type.getClass(__superClass))))
					fieldMap.set(f, f);

				fieldMap.array();
			}
			this.__real_fields = disallowCopy;
			@:privateAccess __interp.__instanceFields = __interp.__instanceFields.concat(disallowCopy);
			__superClass.__real_fields = this.__real_fields;
			__superClass.__class__fields = this.__class__fields;
			__superClass.__interp = this.__interp;
		}
	}

	public function call(name:String, ?args:Array<Dynamic>, ?toSuper:Bool = false):Dynamic {
		var superFnName:Null<String> = toSuper ? '_HX_SUPER__$name' : null;
		var fn:Dynamic = {
			if(toSuper && __interp.variables.exists(superFnName)) {
				__interp.variables.get(superFnName);
			}
			else
				__interp.variables.get(name);
		};

		if (fn != null && Reflect.isFunction(fn))
			return UnsafeReflect.callMethodUnsafe(null, fn, (args == null) ? [] : args);

		// If not found in current class, try parent class recursively
		if (__superClass != null && __superClass is CustomClass)
			return cast(__superClass, CustomClass).call(name, args, toSuper);

		if (hasStaticField(name)) {
			var sfn = __class.getField(name);
			if (sfn != null && Reflect.isFunction(sfn))
				return UnsafeReflect.callMethodUnsafe(null, sfn, (args == null) ? [] : args);
		}

		if (__interp.specialObject != null && __interp.specialObject.obj != null) {
			var parentObj = __interp.specialObject.obj;
			var pfn:Dynamic = UnsafeReflect.field(parentObj, name);
			if (pfn == null)
				pfn = UnsafeReflect.getProperty(parentObj, name);
			if (pfn != null && Reflect.isFunction(pfn))
				return UnsafeReflect.callMethodUnsafe(parentObj, pfn, (args == null) ? [] : args);
		}

		__interp.error(ECustom('$name doesn\'t exist or is not a function'));
		return null;
	}

	public function hasField(name:String):Bool {
		if (__class__fields.contains(name))
			return true;
		if (__superClass != null)
			return superHasField(name);
		return false;
	}

	public function hasStaticField(name:String):Bool {
		return __class.hasField(name);
	}

	function getField(name:String, allowProperty:Bool = true):Dynamic {
		// Allowing to Access Haxe Classes ??????
		var f = __interp.variables.exists(name) ? __interp.variables.get(name) : (__interp.publicVariables != null && __interp.publicVariables.exists(name) ? __interp.publicVariables.get(name) : null);
		if (f == null && __superClass != null && superHasField(name)) {
			if (__superClass is IHScriptCustomAccessBehaviour) {
				f = cast(__superClass, IHScriptCustomAccessBehaviour).hget(name);
			} else {
				f = UnsafeReflect.getProperty(__superClass, name);
				if (f == null)
					f = UnsafeReflect.field(__superClass, name);
			}
		}
		if (f != null && allowProperty && f is Property) {
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
		if (f != null && f is Property) {
			var prop:Property = cast f;
			//prop.__allowSetGet = this.__allowSetGet;
			var r = prop.set(val, !__allowSetGet);
			//prop.__allowSetGet = true;
			return r;
		}
		if (__interp.publicVariables != null && __interp.publicVariables.exists(name)) {
			__interp.publicVariables.set(name, val);
		}
		__interp.variables.set(name, val);
		return val;
	}

	/**
	 * Overrides (replaces) the declared function.
	 * @param name 
	 * @param func 
	 */
	function overrideField(name:String, func:Function) {
		var f = getField(name, false);
		if(f != null && Reflect.isFunction(f)) {
			__interp.variables.set(name, func);
			__interp.variables.set('_HX_SUPER__$name', f);
		}
		else if(__superClass != null && __superClass is CustomClass) {
			cast(__superClass, CustomClass).overrideField(name, func);
		}
	}

	function superHasField(name:String) {
		if (__superClass == null)
			return false;

		var realFieldExists = __superClass.__real_fields != null && __superClass.__real_fields.contains(name);
		var classFieldExists = __superClass.__class__fields != null && __superClass.__class__fields.contains(name);

		if(!realFieldExists && !classFieldExists && __superClass is CustomClass)
			return cast(__superClass, CustomClass).superHasField(name);

		return realFieldExists || classFieldExists;
	}

	function getSuperFields():Array<String> {
		if(__superClass == null) return [];

		var classFields:Map<String, String> = []; // Prevents duplicated values
		var cls:Null<IHScriptCustomClassBehaviour> = __superClass;

		while (cls != null) {
			for(fieldSet in [cls.__class__fields, cls.__real_fields])
				for(f in fieldSet)
					classFields.set(f, f);
			var next:IHScriptCustomClassBehaviour = null;
			if(cls is CustomClass)
				next = cast(cls, CustomClass).__superClass;
			if (next == null)
				break;
			cls = next;
		}

		return [for(f in classFields) f];
	}

	public function hget(name:String):Dynamic {
		switch (name) {
			case 'superClass': return __superClass;
			case 'superConstructor': return __constructor;
			default:
				if (hasField(name))
					return getField(name);

				if (hasStaticField(name)) {
					// Allow static variable access.
					return __class.getField(name);
				}

				if (__superClass != null) {
					if (superHasField(name)) {
						if (__superClass is IHScriptCustomAccessBehaviour) {
							cast(__superClass, IHScriptCustomAccessBehaviour).__allowSetGet = this.__allowSetGet;
							return cast(__superClass, IHScriptCustomAccessBehaviour).hget(name);
						} else {
							var v = UnsafeReflect.getProperty(__superClass, name);
							if (v == null)
								v = UnsafeReflect.field(__superClass, name);
							return v;
						}
					}
				}

				// Allow getting parent object variable
				if (__interp.specialObject != null && __interp.specialObject.obj != null) {
					var parentObj = __interp.specialObject.obj;
					var v = UnsafeReflect.getProperty(parentObj, name);
					if (v == null)
						v = UnsafeReflect.field(parentObj, name);
					if (v != null)
						return v;
				}

				throw "field '"
					+ name
					+ "' does not exist in custom class '"
					+ this.className
					+ "'"
					+ (__superClass != null ? "' or super class '" + Type.getClassName(Type.getClass(this.__superClass)) + "'" : "");
		}
		return null;
	}

	public function hset(name:String, val:Dynamic):Dynamic {
		if (hasField(name))
			return setField(name, val);

		if (hasStaticField(name)) {
			// Allow static variable access.
			return __class.setField(name, val);
		}

		if (__superClass != null) {
			if (superHasField(name)) {
				if (__superClass is IHScriptCustomAccessBehaviour) {
					cast(__superClass, IHScriptCustomAccessBehaviour).__allowSetGet = this.__allowSetGet;
					return cast(__superClass, IHScriptCustomAccessBehaviour).hset(name, val);
				} else {
					var v = UnsafeReflect.getProperty(__superClass, name);
					if (v == null)
						UnsafeReflect.setField(__superClass, name, val);
						
					if (v != null)
						UnsafeReflect.setProperty(__superClass, name, val);
					return val;
				}
			}
		} else if(__class.extend != null && initializing) {
			cacheFieldSet(name, val);
			return val;
		}

		// Allow changing parent object variable (Property and Field Check lol)
		if (__interp.specialObject != null && __interp.specialObject.obj != null) {
			var parentObj = __interp.specialObject.obj;
			var v = UnsafeReflect.getProperty(parentObj, name);
			if (v == null)
				UnsafeReflect.setField(parentObj, name, val);
				
			if (v != null)
				UnsafeReflect.setProperty(parentObj, name, val);
			return val;
		}

		throw "field '"
			+ name
			+ "' does not exist in custom class '"
			+ this.className
			+ "'"
			+ (__superClass != null ? "' or super class '" + Type.getClassName(Type.getClass(this.__superClass)) + "'" : "");

		return null;
	}

	// UNUSED
	public function __callGetter(name:String):Dynamic {
		return null;
	}

	public function __callSetter(name:String, val:Dynamic):Dynamic {
		return null;
	}

	/**
	 * Returns the real superClass if the Custom Class
	 * extends another Custom Class, and so on until
	 * it reaches a real class, otherwise it will
	 * return the last fetched Custom Class
	 * @return Null<Dynamic>
	 */
	public function getSuperclass():IHScriptCustomClassBehaviour {
		if(__superClass == null) return null;

		var cls:Null<IHScriptCustomClassBehaviour> = __superClass;

		// Check if the superClass is another custom class,
		// so it will find for a real class, otherwise
		// returns the last super CustomClass parent.
		while (cls != null && cls is CustomClass) {
			var next = cast(cls, CustomClass).__superClass;
			if (next == null)
				break; // Return the Custom Class itself
			cls = next;
		}
		return cls is CustomClass ? this : cls;
	}

	// TODO: scripted safe cast for custom classes
	public function getUpperclass():IHScriptCustomClassBehaviour {
		if(__upperClass == null) return this;

		var cls:CustomClass = cast __upperClass;

		while (cls != null) {
			var prev:CustomClass = cast cls.__upperClass;
			if(prev == null)
				break;
			cls = prev;
		}

		return cls;
	}

	// TODO: scriptable "toString" function
	public function toString():String
		return className;
}
