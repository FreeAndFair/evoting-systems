/*
 * Copyright (c) 2012 chick307 <chick307@gmail.com>
 *
 * Licensed under the MIT License.
 * http://opensource.org/licenses/mit-license
 */

describe('adler32cs', function() {
	var adler32cs = typeof window === 'object' ?
		window.adler32cs : require('.');

	var _Uint8Array = typeof Uint8Array === 'function' ? Uint8Array : Object;

	var data = [
		{
			binaryString: '\x00',
			utf8String: '\u0000',
			buffer: new _Uint8Array([0]).buffer,
			adler32: 65537
		},
		{
			utf8String: 'あいうえお',
			buffer: new _Uint8Array([
				227, 129, 130, 227, 129, 132, 227, 129,
				134, 227, 129, 136, 227, 129, 138
			]).buffer,
			adler32: 1312033171
		},
		{
			binaryString: 'abc',
			utf8String: 'abc',
			adler32: 38600999
		}
	];

	data.forEach(function(d) {
		if (d.binaryString != null) {
			var name = 'from(' + JSON.stringify(d.binaryString) +
				') needs to be ' + d.adler32 + '.';
			it(name, function() {
				var checksum = adler32cs.from(d.binaryString);
				equals(checksum, d.adler32);
			});
		}
	});

	data.forEach(function(d) {
		if (d.utf8String != null) {
			var name = 'fromUtf8(' + JSON.stringify(d.utf8String) +
				') needs to be ' + d.adler32 + '.';
			it(name, function() {
				var checksum = adler32cs.fromUtf8(d.utf8String);
				equals(checksum, d.adler32);
			});
		}
	});

	if (!!adler32cs.fromBuffer) {
		data.forEach(function(d) {
			if (d.buffer != null) {
				var name = 'fromBuffer(buffer of ' +
					JSON.stringify(d.binaryString || d.utf8String) +
					') needs to be ' + d.adler32 + '.';
				it(name, function() {
					var checksum = adler32cs.fromBuffer(d.buffer);
					equals(checksum, d.adler32);
				});
			}
		});
	}

	it('Adler32() throws TypeError', function() {
		throws(function() {
			adler32cs.Adler32();
		}, TypeError);
	});

	it('Adler32.from() throws TypeError', function() {
		throws(function() {
			adler32cs.Adler32.from();
		}, TypeError);
	});

	it('Adler32.fromUtf8() throws TypeError', function() {
		throws(function() {
			adler32cs.Adler32.fromUtf8();
		}, TypeError);
	});

	it('Adler32.fromBuffer() throws TypeError', function() {
		throws(function() {
			adler32cs.Adler32.fromBuffer();
		}, TypeError);
	});

	data.forEach(function(d) {
		if (d.binaryString != null) {
			var name = 'new Adler32.from(' + JSON.stringify(d.binaryString) +
				').checksum needs to be ' + d.adler32 + '.';
			it(name, function() {
				var c = new adler32cs.Adler32.from(d.binaryString);
				equals(c.checksum, d.adler32);
			});
		}
	});

	data.forEach(function(d) {
		if (d.utf8String != null) {
			var name = 'new Adler32.fromUtf8(' + JSON.stringify(d.utf8String) +
				').checksum needs to be ' + d.adler32 + '.';
			it(name, function() {
				var c = new adler32cs.Adler32.fromUtf8(d.utf8String);
				equals(c.checksum, d.adler32);
			});
		}
	});

	if (!!adler32cs.fromBuffer) {
		data.forEach(function(d) {
			if (d.buffer != null) {
				var name = 'new Adler32.fromBuffer(buffer of ' +
					JSON.stringify(d.binaryString || d.utf8String) +
					').checksum needs to be ' + d.adler32 + '.';
				it(name, function() {
					var c = new adler32cs.Adler32.fromBuffer(d.buffer);
					equals(c.checksum, d.adler32);
				});
			}
		});
	}

	data.forEach(function(d) {
		if (d.binaryString != null) {
			var name = 'new Adler32().update(' + JSON.stringify(d.binaryString) +
				') needs to be ' + d.adler32 + '.';
			it(name, function() {
				var c = new adler32cs.Adler32();
				for (var i = 0; i < d.binaryString.length; i++)
					c.update(d.binaryString.charAt(i));
				equals(c.checksum, d.adler32);
			});
		}
	});

	data.forEach(function(d) {
		if (d.utf8String != null) {
			var name = 'new Adler32().updateUtf8(' +
				JSON.stringify(d.utf8String) +
				') needs to be ' + d.adler32 + '.';
			it(name, function() {
				var c = new adler32cs.Adler32();
				for (var i = 0; i < d.utf8String.length; i++)
					c.updateUtf8(d.utf8String.charAt(i));
				equals(c.checksum, d.adler32);
			});
		}
	});

	if (!!adler32cs.fromBuffer) {
		data.forEach(function(d) {
			if (d.buffer != null) {
				var name = 'new Adler32().updateBuffer(buffer of ' +
					JSON.stringify(d.binaryString || d.utf8String) +
					') needs to be ' + d.adler32 + '.';
				it(name, function() {
					var c = new adler32cs.Adler32();
					var checksum = c.updateBuffer(d.buffer);
					equals(checksum, d.adler32);
					equals(c.checksum, d.adler32);
				});
			}
		});
	}

	function equals(actual, expected) {
		if (actual !== expected) {
			var error = new Error(
				'Expected ' + expected + ' but was ' + actual + '.');
			error.name = 'AssertionError';
			throw error;
		}
	}

	function throws(func, ErrorType) {
		var error = null;
		try {
			func();
		} catch (err) {
			error = err;
		}

		if (error === null) {
			var e = new Error(
				func + 'needs to throw ' + (ErrorType || 'a error.'));
			e.name = 'AssertionError';
			throw e;
		} else if (ErrorType != null && !(error instanceof ErrorType)) {
			var e = new Error(func + 'needs to throw ' + ErrorType.name);
			e.name = 'AssertionError';
			throw e;
		}
	}
});
