package hscript;

import haxe.ds.*;
import haxe.Constraints.IMap;
import haxe.Exception;
import haxe.Timer;
import hscript.Expr;
import hscript.CustomClass;
import hscript.CustomClassHandler;
#if sys
import sys.FileSystem;
import sys.io.File;
#end
using StringTools;

@:structInit
@:access(hscript.Interp)
@:access(hscript.Parser)
@:access(hscript.CustomClassHandler)
@:access(hscript.CustomClass)
@:keepSub
class SScript {
	public static var IGNORE_RETURN(default, never):Dynamic = "###SSCRIPT_IGNORE_RETURN";
	public static var STOP_RETURN(default, never):Dynamic = "###SSCRIPT_STOP_RETURN";

	public static var defaultTypeCheck(default, set):Null<Bool> = true;
	public static var defaultDebug(default, set):Null<Bool> = #if debug true #else null #end;

	public static var globalVariables:SScriptGlobalMap = new SScriptGlobalMap();
	public static var global(default, null):Map<String, SScript> = [];

	static var IDCount(default, null):Int = 0;
	static var BlankReg(get, never):EReg;

	public var customOrigin(default, set):String;
	public var returnValue(default, null):Null<Dynamic> = null;
	public var ID(default, null):Null<Int> = null;
	public var typeCheck:Bool = false;
	public var lastReportedTime(default, null):Float = -1;
	public var lastReportedCallTime(default, null):Float = -1;
	public var notAllowedClasses(default, null):Array<Class<Dynamic>> = [];
	public var variables(get, never):Map<String, Dynamic>;

	public var interp(default, null):Interp;
	public var parser(default, null):Parser;
	public var script(default, null):String = "";
	public var active:Bool = true;
	public var scriptFile(default, null):String = "";
	public var traces:Bool = false;
	public var debugTraces:Bool = #if debug true #else false #end;
	public var parsingException(default, null):SScriptException;
	public var packagePath(get, null):String = "";

    public var instance:Dynamic = {};
    public var mainClassName:String = null;
    public var mainClassHandler:CustomClassHandler = null;
    public var args:Array<Dynamic> = null;

	@:deprecated("parsingExceptions are deprecated, use parsingException instead")
	var parsingExceptions(get, never):Array<Exception>;

	@:noPrivateAccess var _destroyed(default, null):Bool = false;

	public function new(?scriptPath:String = "", ?preset:Bool = true, ?startExecute:Bool = true, ?args:Array<Dynamic>) {
        var time = Timer.stamp();
        this.args = args;
        if (defaultTypeCheck != null)
			typeCheck = defaultTypeCheck;
		if (defaultDebug != null)
			debugTraces = defaultDebug;

		interp = new Interp();
		interp.setScr(this);

		parser = new Parser();
		parser.allowTypes = true;
		parser.allowMetadata = true;

		if (preset) {
			if (debugTraces) trace('SScript constructor: calling preset()');
			this.preset();
		} else {
			if (debugTraces) trace('SScript constructor: preset skipped');
		}

		for (i => k in globalVariables) {
			if (i != null)
				set(i, k);
		}

		try {
			doFile(scriptPath);
			if (startExecute) {
				if (debugTraces) trace('SScript constructor: calling execute()');
				execute();
			} else {
				if (debugTraces) trace('SScript constructor: execute skipped (will be called later)');
			}
			lastReportedTime = Timer.stamp() - time;

			if (debugTraces && scriptPath != null && scriptPath.length > 0) {
				if (lastReportedTime == 0)
					trace('SScript instance created instantly (0s)');
				else
					trace('SScript instance created in ${lastReportedTime}s');
			}
		} catch (e:Dynamic) {
			lastReportedTime = -1;
			parsingException = SScriptException.fromDynamic(e);
			if (debugTraces) trace('SScript constructor error: $e');
		}
	}

	public function execute():Void {
		if (_destroyed) {
			if (traces) trace('SScript execute: destroyed');
			return;
		}

		if (interp == null || !active) {
			if (traces) trace('SScript execute: interp null or not active');
			return;
		}

		var origin:String = {
			if (customOrigin != null && customOrigin.length > 0)
				customOrigin;
			else if (scriptFile != null && scriptFile.length > 0)
				scriptFile;
			else
				"SScript";
		};

		if (script != null && script.length > 0) {
			if (traces) trace('SScript execute: about to run script, origin=' + origin);
			resetInterp();

			try {
            var expr:Expr = parser.parseString(script, origin);
            var r = interp.execute(expr);
            
            // Determine main class name from file name
            if (mainClassName == null && scriptFile != null && scriptFile.length > 0) {
                var fName = scriptFile;
                var slash = fName.lastIndexOf("/");
                var bslash = fName.lastIndexOf("\\");
                var sep = slash > bslash ? slash : bslash;
                if (sep != -1) fName = fName.substr(sep + 1);
                var dot = fName.lastIndexOf(".");
                if (dot != -1) fName = fName.substr(0, dot);
                mainClassName = fName;
            }
            
            // Instantiate the main class
            if (mainClassName != null && interp.customClasses.exists(mainClassName)) {
                mainClassHandler = interp.customClasses.get(mainClassName);
                instance = mainClassHandler.hnew(args != null ? args : []);
            } else {
                // Fallback: pick the first defined class if names don't match
                for (k => v in interp.customClasses) {
                    mainClassName = k;
                    mainClassHandler = v;
                    instance = v.hnew(args != null ? args : []);
                    break;
                }
            }
            
            returnValue = r;
            if (traces) trace('SScript execute: success');
        } catch (e:Dynamic) {
				parsingException = SScriptException.fromDynamic(e);
				returnValue = null;
				if (traces) trace('SScript execute error: $e');
			}
		} else {
			if (traces) trace('SScript execute: no script');
		}
	}

	public function set(key:String, obj:Dynamic):SScript {
        if (_destroyed) return null;
        if (obj != null && (obj is Class) && notAllowedClasses.contains(obj))
            throw 'Tried to set ${Type.getClassName(obj)} which is not allowed.';
        if (key == null) return this;
        if (Tools.keys.contains(key)) throw '$key is a keyword, set something else';

        var handled = false;

        // 1. Force update through the ENTIRE CustomClass inheritance chain (Fixes 'null' inheritance issues)
        if (instance != null && instance != {}) {
            if (Std.isOfType(instance, CustomClass)) {
                try {
                    var current:Dynamic = instance;
                    // Traverse from Child -> Parent -> Grandparent, injecting the variable everywhere
                    while (current != null && Std.isOfType(current, CustomClass)) {
                        var cc = cast(current, CustomClass);
                        @:privateAccess {
                            if (cc.__interp != null && cc.__interp.variables != null) {
                                cc.__interp.variables.set(key, obj);
                            }
                        }
                        try { cc.hset(key, obj); } catch(e:Dynamic) {}
                        
                        // Use our backdoor to securely grab the next class up the chain
                        current = cc.hget("superClassRaw"); 
                    }
                    handled = true;
                } catch(e:Dynamic) {}
            } else {
                try {
                    Reflect.setProperty(instance, key, obj);
                    handled = true;
                } catch(e:Dynamic) {}
            }
        }
        
        // 2. Target main class handler static fields
        if (!handled && mainClassHandler != null && mainClassHandler.hasField(key)) {
            try { 
                mainClassHandler.hset(key, obj); 
                handled = true; 
            } catch(e:Dynamic) {}
        }
        
        // 3. Fallback to global interpreter maps
        if (interp != null) {
            if (interp.allowStaticVariables && interp.staticVariables != null)
                interp.staticVariables.set(key, obj);
            if (interp.allowPublicVariables && interp.publicVariables != null)
                interp.publicVariables.set(key, obj);
            if (interp.variables != null)
                interp.variables.set(key, obj);
        }

        return this;
    }

	public function setClass(cl:Class<Dynamic>):SScript {
		if (_destroyed)
			return null;

		if (cl == null) {
			if (traces)
				trace('Class cannot be null');
			return null;
		}

		var clName:String = Type.getClassName(cl);
		if (clName != null) {
			var splitCl:Array<String> = clName.split('.');
			if (splitCl.length > 1)
				clName = splitCl[splitCl.length - 1];
			set(clName, cl);
		}
		return this;
	}

	public function setClassString(cl:String):SScript {
		if (_destroyed)
			return null;

		if (cl == null || cl.length < 1) {
			if (traces)
				trace('Class cannot be null');
			return null;
		}

		var cls:Class<Dynamic> = Type.resolveClass(cl);
		if (cls != null) {
			if (cl.split('.').length > 1)
				cl = cl.split('.')[cl.split('.').length - 1];
			set(cl, cls);
		}
		return this;
	}

	public function setSpecialObject(obj:Dynamic, ?includeFunctions:Bool = true, ?exclusions:Array<String>):SScript {
		if (_destroyed)
			return null;
		if (!active)
			return this;
		if (obj == null)
			return this;
		if (exclusions == null)
			exclusions = new Array();

		var types:Array<Dynamic> = [Int, String, Float, Bool, Array];
		for (i in types)
			if (Std.isOfType(obj, i))
				throw 'Special object cannot be ${i}';

		interp.specialObject = {obj: obj, includeFunctions: includeFunctions, exclusions: exclusions.copy()};
		return this;
	}

	public function locals():Map<String, Dynamic> {
		if (_destroyed)
			return null;

		if (!active)
			return [];

		var newMap:Map<String, Dynamic> = new Map();
		if (interp.locals != null) {
			for (i in interp.locals.keys()) {
				var v = interp.locals[i];
				if (v != null)
					newMap[i] = v.r;
			}
		}
		return newMap;
	}

	public function unset(key:String):SScript {
        if (_destroyed || interp == null || !active || key == null) return null;
        
        var handled = false;
        if (mainClassHandler != null && mainClassHandler.hasField(key)) {
            try { mainClassHandler.hset(key, null); handled = true; } catch(e:Dynamic) {}
        }
        if (!handled && instance != null && instance != {}) {
            if (Std.isOfType(instance, CustomClass)) {
                try { cast(instance, CustomClass).hset(key, null); handled = true; } catch(e:Dynamic) {}
            } else {
                try { Reflect.setProperty(instance, key, null); handled = true; } catch(e:Dynamic) {}
            }
        }
        
        if (!handled) {
            if (interp.allowStaticVariables && interp.staticVariables.exists(key)) {
                interp.staticVariables.remove(key);
            } else if (interp.allowPublicVariables && interp.publicVariables.exists(key)) {
                interp.publicVariables.remove(key);
            } else if (interp.variables.exists(key)) {
                interp.variables.remove(key);
            }
        }
        return this;
    }

	public function get(key:String):Dynamic {
        if (_destroyed) return null;
        
        // 1. Prioritize reading from CustomClass inheritance chain
        if (instance != null && instance != {}) {
            if (Std.isOfType(instance, CustomClass)) {
                try {
                    var cc = cast(instance, CustomClass);
                    
                    // Look through child -> superclass chain for the most accurate value
                    var current:Dynamic = cc;
                    while (current != null && Std.isOfType(current, CustomClass)) {
                        @:privateAccess {
                            if (current.__interp != null && current.__interp.variables != null && current.__interp.variables.exists(key)) {
                                return current.__interp.variables.get(key);
                            }
                            current = current.__superClass;
                        }
                    }
                    return cc.hget(key);
                } catch(e:Dynamic) {}
            } else {
                try {
                    if (Reflect.hasField(instance, key))
                        return Reflect.getProperty(instance, key);
                } catch(e:Dynamic) {}
            }
        }

        if (mainClassHandler != null && mainClassHandler.hasField(key)) {
            try { return mainClassHandler.hget(key); } catch(e:Dynamic) {}
        }
        
        if (interp != null) {
            var l = locals();
            if (l.exists(key)) return l[key];
            
            if (interp.allowStaticVariables && interp.staticVariables.exists(key))
                return interp.staticVariables.get(key);
            if (interp.allowPublicVariables && interp.publicVariables.exists(key))
                return interp.publicVariables.get(key);
            if (interp.variables.exists(key))
                return interp.variables.get(key);
        }
        return null;
    }

	public function call(func:String, ?args:Array<Dynamic>):FunctionCall {
        if (_destroyed) return { exceptions: [new SScriptException(new Exception((if (scriptFile != null && scriptFile.length > 0) scriptFile else "SScript instance") + " is destroyed."))], calledFunction: func, succeeded: false, returnValue: null };
        if (!active) return { exceptions: [new SScriptException(new Exception((if (scriptFile != null && scriptFile.length > 0) scriptFile else "SScript instance") + " is not active."))], calledFunction: func, succeeded: false, returnValue: null };
        
        var time:Float = Timer.stamp();
        var scriptFile:String = if (scriptFile != null && scriptFile.length > 0) scriptFile else "";
        var caller:FunctionCall = { exceptions: [], calledFunction: func, succeeded: false, returnValue: null };
        if (args == null) args = new Array();
        var pushedExceptions:Array<String> = new Array();
        function pushException(e:String) {
            if (!pushedExceptions.contains(e)) caller.exceptions.push(new SScriptException(new Exception(e)));
            pushedExceptions.push(e);
        }
        
        if (func == null) {
            pushException('Function name cannot be null for $scriptFile!');
            return caller;
        }
        
        // --- CRASH-SAFE SUPER CALL INTERCEPTION ---
        // If someone calls script.call("super.update"), safely route it to the superclass!
        if (func.startsWith("super.")) {
            var actualFunc = func.substring(6);
            if (instance != null && Std.isOfType(instance, CustomClass)) {
                try {
                    var cc:CustomClass = cast instance;
                    // true = call superclass specifically
                    var ret = cc.call(actualFunc, args, true); 
                    caller.succeeded = true;
                    caller.returnValue = ret;
                } catch(e:Dynamic) {
                    caller.exceptions.insert(0, SScriptException.fromDynamic(e));
                }
                lastReportedCallTime = Timer.stamp() - time;
                return caller;
            } else {
                pushException('Cannot call super.$actualFunc because instance is not a valid CustomClass.');
                return caller;
            }
        }
        // ------------------------------------------

        var fn:Dynamic = null;
        var targetObj:Dynamic = null;
        
        if (mainClassHandler != null && mainClassHandler.hasField(func)) {
            try {
                fn = mainClassHandler.hget(func);
                targetObj = null; // Static call
            } catch(e:Dynamic) {}
        } 
        if (fn == null && instance != null && instance != {}) {
            if (Std.isOfType(instance, CustomClass)) {
                try {
                    fn = cast(instance, CustomClass).hget(func);
                    targetObj = instance;
                } catch(e:Dynamic) {}
            } else {
                try {
                    fn = Reflect.getProperty(instance, func);
                    targetObj = instance;
                } catch(e:Dynamic) {}
            }
        }
        
        if (fn == null) {
            fn = get(func);
            targetObj = null; // Global function call
        }
        
        if (fn != null && Reflect.isFunction(fn)) {
            try {
                var ret = Reflect.callMethod(targetObj, fn, args);
                caller.succeeded = true;
                caller.returnValue = ret;
            } catch (e:Dynamic) {
                caller.exceptions.insert(0, SScriptException.fromDynamic(e));
            }
        } else {
            pushException('Function $func does not exist in $scriptFile.');
        }
        
        lastReportedCallTime = Timer.stamp() - time;
        return caller;
    }

	public function clear():SScript {
		if (_destroyed)
			return null;
		if (!active)
			return this;

		if (interp == null)
			return this;

		var importantThings:Array<String> = ['true', 'false', 'null', 'trace'];

		for (i in interp.variables.keys())
			if (!importantThings.contains(i))
				interp.variables.remove(i);

		return this;
	}

	public function exists(key:String):Bool {
        if (_destroyed || !active || interp == null) return false;
        
        if (mainClassHandler != null && mainClassHandler.hasField(key)) return true;
        if (instance != null && instance != {}) {
            if (Std.isOfType(instance, CustomClass)) {
                var cc = cast(instance, CustomClass);
                if (cc.__class__fields.contains(key)) return true;
                try { cc.hget(key); return true; } catch(e:Dynamic) {}
            } else {
                if (Reflect.hasField(instance, key)) return true;
            }
        }
        
        var l = locals();
        if (l.exists(key)) return true;
        
        if (interp.allowStaticVariables && interp.staticVariables.exists(key)) return true;
        if (interp.allowPublicVariables && interp.publicVariables.exists(key)) return true;
        if (interp.variables.exists(key)) return true;
        
        return false;
    }

	public function preset():Void {
		if (_destroyed)
			return;
		if (!active)
			return;

        interp.allowStaticVariables = true;
        interp.allowPublicVariables = true;

        interp.variables.set("importScript", function(path:String) {
            var other = new SScript(path, true, true);
            if (other.interp != null) {
                for (k => v in other.interp.customClasses) {
                    interp.customClasses.set(k, v);
                }
                for (k => v in other.interp.variables) {
                    if (!interp.variables.exists(k)) {
                        interp.variables.set(k, v);
                    }
                }
            }
        });

		setClass(Date);
		setClass(DateTools);
		setClass(EReg);
		setClass(Math);
		setClass(Reflect);
		setClass(Std);
		setClass(SScript);
		setClass(StringTools);
		setClass(Type);
		setClass(List);
		setClass(StringBuf);
		setClass(Xml);
		setClass(haxe.Http);
		setClass(haxe.Json);
		setClass(haxe.Log);
		setClass(haxe.Serializer);
		setClass(haxe.Unserializer);
		setClass(haxe.Timer);

		#if sys
		setClass(Sys);
		setClass(sys.FileSystem);
		setClass(sys.io.File);
		setClass(sys.io.Process);
		setClass(sys.io.FileInput);
		setClass(sys.io.FileOutput);
		#end
	}

	function resetInterp():Void {
		if (_destroyed)
			return;
		if (interp == null)
			return;

		interp.locals = new Map();
		while (interp.declared.length > 0)
			interp.declared.pop();
	}

	function doFile(scriptPath:String):Void {
		parsingException = null;

		if (_destroyed)
			return;

		if (scriptPath == null || scriptPath.length < 1 || BlankReg.match(scriptPath)) {
			ID = IDCount + 1;
			IDCount++;
			global[Std.string(ID)] = this;
			return;
		}

		if (scriptPath != null && scriptPath.length > 0) {
			#if sys
			if (FileSystem.exists(scriptPath)) {
				scriptFile = scriptPath;
				script = File.getContent(scriptPath);
			} else {
				scriptFile = "";
				script = scriptPath;
			}
			#else
			scriptFile = "";
			script = scriptPath;
			#end

			if (scriptFile != null && scriptFile.length > 0)
				global[scriptFile] = this;
			else if (script != null && script.length > 0)
				global[script] = this;
		}
	}

	public function doString(string:String, ?origin:String):SScript {
		if (_destroyed)
			return null;
		if (!active)
			return null;
		if (string == null || string.length < 1 || BlankReg.match(string))
			return this;

		parsingException = null;

		var time = Timer.stamp();
		try {
			var og:String = origin;
			if (og != null && og.length > 0)
				customOrigin = og;
			if (og == null || og.length < 1)
				og = customOrigin;
			if (og == null || og.length < 1)
				og = "SScript";

			if (!active || interp == null)
				return null;

			resetInterp();

			try {
            script = string;
            if (scriptFile != null && scriptFile.length > 0) {
                if (ID != null) global.remove(Std.string(ID));
                global[scriptFile] = this;
            } else if (script != null && script.length > 0) {
                if (ID != null) global.remove(Std.string(ID));
                global[script] = this;
            }
            var expr:Expr = parser.parseString(script, og);
            var r = interp.execute(expr);
            
            if (mainClassName == null && og != null && og.length > 0) {
                var fName = og;
                var slash = fName.lastIndexOf("/");
                var bslash = fName.lastIndexOf("\\");
                var sep = slash > bslash ? slash : bslash;
                if (sep != -1) fName = fName.substr(sep + 1);
                var dot = fName.lastIndexOf(".");
                if (dot != -1) fName = fName.substr(0, dot);
                mainClassName = fName;
            }
            
            if (mainClassName != null && interp.customClasses.exists(mainClassName)) {
                mainClassHandler = interp.customClasses.get(mainClassName);
                instance = mainClassHandler.hnew(args != null ? args : []);
            } else {
                for (k => v in interp.customClasses) {
                    mainClassName = k;
                    mainClassHandler = v;
                    instance = v.hnew(args != null ? args : []);
                    break;
                }
            }
            
            returnValue = r;
            if (traces) {
					var execTime = Timer.stamp() - time;
					if (execTime == 0)
						trace('SScript doString executed instantly');
					else
						trace('SScript doString executed in ${execTime}s');
				}
			} catch (e:Dynamic) {
				script = "";
				parsingException = SScriptException.fromDynamic(e);
				returnValue = null;
				if (traces) {
					trace('SScript doString error: $e');
				}
			}

			lastReportedTime = Timer.stamp() - time;
		} catch (e:Dynamic) {
			lastReportedTime = -1;
			parsingException = SScriptException.fromDynamic(e);
			if (traces) {
				trace('SScript doString fatal error: $e');
			}
		}

		return this;
	}

	inline function toString():String {
		if (_destroyed)
			return "null";
		if (scriptFile != null && scriptFile.length > 0)
			return scriptFile;
		return "[SScript SScript]";
	}

	#if (sys)
	public static function listScripts(path:String, ?extensions:Array<String>):Array<SScript> {
		if (!path.endsWith('/'))
			path += '/';

		if (extensions == null || extensions.length < 1)
			extensions = ['hx'];

		var list:Array<SScript> = [];
		if (FileSystem.exists(path) && FileSystem.isDirectory(path)) {
			var files:Array<String> = FileSystem.readDirectory(path);
			for (i in files) {
				var hasExtension:Bool = false;
				for (l in extensions) {
					if (i.endsWith(l)) {
						hasExtension = true;
						break;
					}
				}
				if (hasExtension && FileSystem.exists(path + i))
					list.push(new SScript(path + i));
			}
		}

		return list;
	}
	#else
	public static function listScripts(path:String, ?extensions:Array<String>):Array<SScript> {
		return [];
	}
	#end

	public function stop():Void {
		active = false;
		clear();
		resetInterp();
	}

	public function destroy():Void {
		if (_destroyed)
			return;

		if (global.exists(script) && script != null && script.length > 0)
			global.remove(script);
		if (global.exists(scriptFile) && scriptFile != null && scriptFile.length > 0)
			global.remove(scriptFile);

		clear();
		resetInterp();

		customOrigin = null;
		parser = null;
		interp = null;
		script = null;
		scriptFile = null;
		active = false;
		notAllowedClasses = null;
		lastReportedCallTime = -1;
		lastReportedTime = -1;
		ID = null;
		parsingException = null;
		returnValue = null;
		_destroyed = true;
	}

	function get_variables():Map<String, Dynamic> {
		if (_destroyed)
			return null;
		return interp.variables;
	}

	function get_packagePath():String {
		if (_destroyed)
			return null;
		return packagePath;
	}

	static function get_BlankReg():EReg {
		return ~/^[\n\r\t]$/;
	}

	function set_customOrigin(value:String):String {
		if (_destroyed)
			return null;
		#if hscriptPos
		@:privateAccess parser.origin = value;
		#end
		return customOrigin = value;
	}

	static function set_defaultTypeCheck(value:Null<Bool>):Null<Bool> {
		for (i in global) {
			i.typeCheck = value == null ? false : value;
		}
		return defaultTypeCheck = value;
	}

	static function set_defaultDebug(value:Null<Bool>):Null<Bool> {
		for (i in global) {
			i.debugTraces = value == null ? false : value;
		}
		return defaultDebug = value;
	}

	function get_parsingExceptions():Array<Exception> {
		if (_destroyed)
			return null;
		if (parsingException == null)
			return [];
		return [parsingException.toException()];
	}
}

abstract SScriptException(Exception) {
	public var message(get, never):String;

	public function new(exception:Exception)
		this = exception;

	@:from
	public static function fromException(exception:Exception):SScriptException
		return new SScriptException(exception);

	public static function fromDynamic(e:Dynamic):SScriptException
	{
		if (Std.isOfType(e, Exception))
			return new SScriptException(cast e);
		return new SScriptException(new Exception(Std.string(e)));
	}

	@:to
	public function toString():String
		return message;

	public function details():String
		return this.details();

	function get_message():String
		return Std.string(this);

	public function toException():Exception
		return this;
}

typedef SScriptGlobalMap = SScriptTypedGlobalMap<String, Dynamic>;

@:transitive
@:multiType(@:followWithAbstracts K)
abstract SScriptTypedGlobalMap<K, V>(IMap<K, V>) {
	public function new();

	public inline function set(key:K, value:V) {
		this.set(key, value);

		var key:String = cast key;
		var value:Dynamic = cast value;
		for (i in SScript.global) {
			@:privateAccess
			if (!i._destroyed)
				i.set(key, value);
		}
	}

	@:arrayAccess public inline function get(key:K)
		return this.get(key);

	public inline function exists(key:K)
		return this.exists(key);

	public inline function remove(key:K)
		return this.remove(key);

	public inline function keys():Iterator<K>
		return this.keys();

	public inline function iterator():Iterator<V>
		return this.iterator();

	public inline function keyValueIterator():KeyValueIterator<K, V>
		return this.keyValueIterator();

	public inline function copy():Map<K, V>
		return cast this.copy();

	public inline function toString():String
		return this.toString();

	public inline function clear():Void
		this.clear();

	@:arrayAccess @:noCompletion public inline function arrayWrite(k:K, v:V):V {
		this.set(k, v);
		var key:String = cast k;
		var value:Dynamic = cast v;
		for (i in SScript.global) {
			@:privateAccess
			if (!i._destroyed)
				i.set(key, value);
		}
		return v;
	}

	@:to static inline function toStringMap<K:String, V>(t:IMap<K, V>):StringMap<V>
		return new StringMap<V>();

	@:to static inline function toIntMap<K:Int, V>(t:IMap<K, V>):IntMap<V>
		return new IntMap<V>();

	@:to static inline function toEnumValueMapMap<K:EnumValue, V>(t:IMap<K, V>):EnumValueMap<K, V>
		return new EnumValueMap<K, V>();

	@:to static inline function toObjectMap<K:{}, V>(t:IMap<K, V>):ObjectMap<K, V>
		return new ObjectMap<K, V>();

	@:from static inline function fromStringMap<V>(map:StringMap<V>):SScriptTypedGlobalMap<String, V>
		return cast map;

	@:from static inline function fromIntMap<V>(map:IntMap<V>):SScriptTypedGlobalMap<Int, V>
		return cast map;

	@:from static inline function fromObjectMap<K:{}, V>(map:ObjectMap<K, V>):SScriptTypedGlobalMap<K, V>
		return cast map;
}

typedef FunctionCall = {
	public var succeeded:Bool;
	public var calledFunction:String;
	public var returnValue:Null<Dynamic>;
	public var exceptions:Array<SScriptException>;
}