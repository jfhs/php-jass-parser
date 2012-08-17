<?php
/**
 * JASS Parser by jfhs <romoper@yandex.ru>
 */

class JASSLexer {

	private $input;
	private $tokens;
	private $pos = 0;
	private $stack = array();

	private function remove_comments(&$input) {
		$a = explode("\n", $input);
		foreach($a as &$line) {
			if (strpos($line, '//') !== false) {
				$line = substr($line, 0, strpos('//', $line));
			}
		}
		return implode("\n", $a);;
	}

	public function __construct($input) {
		$input = $this->remove_comments($input);
		$this->input = $input;

		//numbers
		$r = '[0-9]+\\.[0-9]*|\\.[0-9]+';
		$r .= '|[.,;]';

		//logical operators
		$r .= '|(?:<>|<=>|>=|<=|==|=|!=|!|<<|>>|<|>|\\|\\||\\||&&|&|-|\\+|\\*(?!\/)|\/(?!\\*)|\\%|~|\\^|\\?)';

		//brackets, parentheses
		$r .= '|[\\[\\]\\(\\)]';

		//empty quotes
		$r .= '|\\\'\\\'(?!\\\')';
		$r .= '|\\"\\"(?!\\"")';

		//quoted stuff
		$r .= '|"[^"\\\\]*(?:\\\\.[^"\\\\]*)*"';

		//words
		$r .= '|(?:[\w:@]+(?:(?:\w+)?)*)';

		preg_match_all('/' . $r . '/sm', $input, $result);
		$this->tokens = $result[0];
	}

	private $cnt_peeks = 0;
	private $last_pos = 0;

	public function peek() {
		if ($this->pos != $this->last_pos) {
			$this->last_pos = $this->pos;
			$this->cnt_peeks = 0;
		}
		if (++$this->cnt_peeks > 100) {
			throw new Exception("stuck");
		}
		if (!$this->hasMore()) {
			throw new Exception("Requesting more tokens when eof reached");
		}
		return $this->tokens[$this->pos];
	}

	public function next() {
		return $this->tokens[$this->pos++];
	}

	public function hasMore() {
		return $this->pos < count($this->tokens);
	}

	/**
	 * Checks if next token is $token, and if so EATS IT!!
	 *
	 * @param $token
	 * @return bool
	 */
	public function next_is($token) {
		if ($this->peek() == $token) {
			$this->next();
			return true;
		}
		return false;
	}

	public function next_in($array) {
		if (in_array($this->peek(), $array) !== false) {
			return $this->next();
		}
		return false;
	}

	public function match($regex) {
		return preg_match('/^'.$regex.'$/', $this->peek());
	}

	public function expect($token) {
		if ($this->peek() != $token) {
			throw new Exception($token." expected, '".$this->peek()."' found");
		} else {
			$this->next();
		}
	}

	public function push() {
		array_push($this->stack, $this->pos);
	}

	public function pop() {
		array_pop($this->stack);
	}

	public function rollback() {
		$this->pos = array_pop($this->stack);
	}
}

class JASSParser {

	const ID_REGEX = '[a-zA-Z_][a-zA-Z_0-9]*';
	const LP_OPS = '[+\\-><]|==|<=|>=|!=|and|or';
	const HP_OPS = '[\\*\\/]';
	const UNARY_OPS = 'not|[\\-+]';
	const DEC_REGEX = '[1-9][0-9]*';
	const OCT_REGEX = '0[0-9]*';
	const HEX_REGEX = '(\\$[0-9a-fA-F]+|0[xX][0-9a-fA-F]+)';
	const REAL_REGEX = '([0-9]+\\.[0-9]*|\\.[0-9]+)';

	private static $reserved_words = array('function', 'takes', 'returns', 'return', 'nothing',
	                             'endfunction', 'if' ,'else', 'elseif', 'endif', 'loop',
	                             'exitwhen', 'globals', 'endglobals', 'local', 'set',
							     'call', 'constant', 'type', 'extends', 'native', 'array');

	public $types = array();
	public $globals = array();
	public $global_const = array();
	public $functions = array();
	public $natives = array();

	private $params = array();

	public function __construct($params = array()) {
		$this->params = $params;
	}

	public function parse(JASSLexer $lexer) {
		$this->file($lexer);
	}

	private static $simple_types = array('decimal', 'octal', 'hex', 'real');

    /**
     * Tries to calculate expression's value, succeeds if all parts of expression is numeric constants
     *
     * @static
     * @param $expr expression to calculate
     * @return array folded expression, if some part is not a constant, other constant parts can be still calculated
     */
    public static function recursive_calc_expr($expr) {
		if (isset($expr['type'])) {
			return $expr;
		}
		$op = false;
		$calculated = array();
		foreach($expr as $part) {
			if (is_array($part)) {
				$part = self::recursive_calc_expr($part);
				//can't process this :(
				if (!isset($part['type']) || !in_array($part['type'], self::$simple_types)) {
					return $expr;
				}
				if ($op) {
					if (count($calculated) == 0) {
						if ($op == '-') {
							$part['value'] *= -1;
						}
						$calculated = $part;
					} else {
						if ($op == '+') {
							$calculated['value'] += $part['value'];
						} elseif ($op == '-') {
							$calculated['value'] -= $part['value'];
						} elseif ($op == '*') {
							$calculated['value'] *= $part['value'];
						} elseif ($op == '/') {
							$calculated['value'] /= $part['value'];
						}
					}
				} else {
					$calculated = $part;
				}
			} else {
				$op = $part;
			}
		}
		//just for safety
		$calculated['type'] = 'real';
		return $calculated;
	}

	protected function file(JASSLexer $lexer) {
		while($this->declaration($lexer));
		while($this->func($lexer));
	}

	protected function func(JASSLexer $lexer) {
		if (!$lexer->hasMore()) {
			return false;
		}
		$is_const = $lexer->next_is('constant');
		$lexer->expect('function');
		$data = $this->func_declr($lexer);
		$locals = $this->local_var_list($lexer);
		$statements = array();
		while(!$lexer->next_is('endfunction')) {
			$statements[] = $this->statement($lexer);
		}
		$this->functions[] = array(
			'is_const' => $is_const,
			'declaration' => $data,
			'locals' => $locals,
			'statements' => $statements,
		);
		return true;
	}

	protected function func_declr(JASSLexer $lexer) {
		$id = $this->id($lexer);
		$lexer->expect('takes');
		$args = $this->args_declaration($lexer);
		$lexer->expect('returns');
		if ($lexer->next_is('nothing')) {
			$return = false;
		} else {
			$return = $this->id($lexer);
		}
		return array(
			'id' => $id,
			'args' => $args,
			'return' => $return,
		);
	}

	protected function local_var_list(JASSLexer $lexer) {
		$result = array();
		while($lexer->next_is('local')) {
			$result[] = $this->var_declr($lexer);
		}
		return $result;
	}

	protected function statement(JASSLexer $lexer) {
		if ($ret = $this->set($lexer)) {
			return $ret;
		}
		if ($ret = $this->call($lexer)) {
			return $ret;
		}
		if ($ret = $this->ifthenelse($lexer)) {
			return $ret;
		}
		if ($ret = $this->loop($lexer)) {
			return $ret;
		}
		if ($ret = $this->exitwhen($lexer)) {
			return $ret;
		}
		if ($ret = $this->ret($lexer)) {
			return $ret;
		}
		if ($ret = $this->debug($lexer)) {
			return $ret;
		}
		return false;
	}

	protected function set(JASSLexer $lexer) {
		if (!$lexer->next_is('set')) {
			return false;
		}
		$id = $this->id($lexer);
		$index = false;
		if ($lexer->next_is('[')) {
			$index = $this->expr($lexer);
			$lexer->expect(']');
		}
		$lexer->expect('=');
		$val = $this->expr($lexer);
		return array(
			'type' => 'set',
			'id' => $id,
			'index' => $index,
			'value' => $val,
		);
	}

	protected function call(JASSLexer $lexer) {
		if (!$lexer->next_is('call')) {
			return false;
		}
		$id = $this->id($lexer);
		$args = $this->args($lexer);
		if (isset($this->params['call_cb'])) {
			$fn = $this->params['call_cb'];
            call_user_func($fn, $id, $args);
		}
		return array(
			'type' => 'call',
			'id' => $id,
			'args' => $args,
		);
	}

	protected function ifthenelse(JASSLexer $lexer) {
		if (!$lexer->next_is('if')) {
			return false;
		}
		$result = array();
		$expr = $this->expr($lexer);
		$lexer->expect('then');
		$statements = array();
		$expected = array('else', 'elseif', 'endif');
		while(true) {
			while(($next = $lexer->next_in($expected)) === false) {
				$statements[] = $this->statement($lexer);
			}
			$result[] = array(
				'condition' => $expr,
				'statements' => $statements,
			);
			if ($next == 'endif') {
				break;
			} elseif ($next == 'elseif') {
				$expr = $this->expr($lexer);
				$lexer->expect('then');
			} elseif ($next == 'else') {
				$expr = false;
				$expected = array('endif');
			}
		}
		return array(
			'type' => 'if',
			'branches' => $result,
		);
	}

	protected function loop(JASSLexer $lexer) {
		if (!$lexer->next_is('loop')) {
			return false;
		}
		$statements = array();
		while(!$lexer->next_is('endloop')) {
			$statements[] = $this->statement($lexer);
		}
		return array(
			'type' => 'loop',
			'statements' => $statements,
		);
	}

	protected function exitwhen(JASSLexer $lexer) {
		if (!$lexer->next_is('exitwhen')) {
			return false;
		}
		$expr = $this->expr($lexer);
		return array(
			'type' => 'exitwhen',
			'condition' => $expr,
		);
	}

	protected function ret(JASSLexer $lexer) {
		if (!$lexer->next_is('return')) {
			return false;
		}
		$expr = $this->expr($lexer);
		return array(
			'type' => 'return',
			'expr' => $expr,
		);
	}

	protected function debug(JASSLexer $lexer) {
		if (!$lexer->next_is('debug')) {
			return false;
		}
		if ($ret = $this->set($lexer)) {
		} elseif ($ret = $this->call($lexer)) {
		} elseif ($ret = $this->ifthenelse($lexer)) {
		} elseif ($ret = $this->loop($lexer)) {
		}
		if ($ret) {
			return array(
				'type' => 'debug',
				'sub' => $ret,
			);
		}
		return false;
	}

	protected function args_declaration(JASSLexer $lexer) {
		if ($lexer->next_is('nothing')) {
			return array();
		}
		$result = array();
		do {
			$type = $this->id($lexer);
			$id = $this->id($lexer);
			$result[$id] = $type;
		} while($lexer->next_is(','));
		return $result;
	}

	protected function declaration(JASSLexer $lexer) {
		if (!$lexer->hasMore()) {
			return false;
		}
		return ($this->typedef($lexer) || $this->globals($lexer) || $this->native($lexer));
	}

	protected function native(JASSLexer $lexer) {
		$lexer->push();
		try {
			$constant = $lexer->next_is('constant');
			$lexer->expect('native');
			$declr = $this->func_declr($lexer);
			$this->natives[] = $declr;
			$lexer->pop();
			return true;
		} catch (Exception $e) {
			$lexer->rollback();
			return false;
		}
	}

	protected function typedef(JASSLexer $lexer) {
		if (!$lexer->next_is('type')) {
			return false;
		}
		$type_name = $this->id($lexer);
		$lexer->expect('extends');
		$base_name = $this->id($lexer);
		$types[$type_name] = $base_name;
		return true;
	}

	protected function globals(JASSLexer $lexer) {
		if (!$lexer->next_is('globals')) {
			return false;
		}
		while(!$lexer->next_is('endglobals')) {
			$this->global_var($lexer);
		}
		return true;
	}

	protected function global_var(JASSLexer $lexer) {
		if ($lexer->next_is('constant')) {
			$type = $this->id($lexer);
			$id = $this->id($lexer);
			$lexer->expect('=');
			$val = $this->expr($lexer);
			$this->global_const[$id] = array(
				'type' => $type,
				'value' => $val,
			);
			return true;
		} else {
			return $this->var_declr($lexer);
		}
	}

	protected function var_declr(JASSLexer $lexer) {
		if (($type = $this->id($lexer)) === false) {
			return false;
		}
		$is_array = $lexer->next_is('array');
		$id = $this->id($lexer);
		$this->globals[$id] = array(
			'type' => $type,
			'is_array' => $is_array,
		);
		if (!$is_array) {
			if ($lexer->next_is('=')) {
				$this->globals[$id]['value'] = $this->expr($lexer);
			}
		}
		return true;
	}

	protected function expr(JASSLexer $lexer) {
		if ($lexer->match(self::UNARY_OPS)) {
			$op = $lexer->next();
			$term = $this->term($lexer);
			$term = array($op, $term);
		} else {
			$term = $this->term($lexer);
		}
		$result = array($term);
		while ($lexer->match(self::LP_OPS)) {
			$op = $lexer->next();
			$result[] = $op;
			$result[] = $this->term($lexer);
		}
		if (count($result) == 1) {
			return $result[0];
		}
		return $result;
	}

	protected function term(JASSLexer $lexer) {
		$term = $this->factor($lexer);
		$result = array($term);
		while ($lexer->match(self::HP_OPS)) {
			$op = $lexer->next();
			$result[] = $op;
			$result[] = $this->factor($lexer);
		}
		if (count($result) == 1) {
			return $result[0];
		}
		return $result;
	}

	protected function factor(JASSLexer $lexer) {
		if ($ret = $this->constant($lexer)) {
			return $ret;
		}
		if ($ret = $this->array_ref($lexer)) {
			return $ret;
		}
		if ($ret = $this->func_ref($lexer)) {
			return $ret;
		}
		if ($ret = $this->func_call($lexer)) {
			return $ret;
		}
		if ($ret = $this->parenthesis($lexer)) {
			return $ret;
		}
		if ($ret = $this->id($lexer)) {
			return array(
				'type' => 'var',
				'id' => $ret,
			);
		}
		return false;
	}

	protected function constant(JASSLexer $lexer) {
		if ($lexer->next_is('null')) {
			return array(
				'type' => 'null',
			);
		}
		if ($ret = $this->int_constant($lexer)) {
			return $ret;
		}
		if ($ret = $this->real_constant($lexer)) {
			return $ret;
		}
		if ($ret = $this->bool_constant($lexer)) {
			return $ret;
		}
		if ($ret = $this->string_constant($lexer)) {
			return $ret;
		}
		return false;
	}

	protected function int_constant(JASSLexer $lexer) {
		if ($lexer->match(self::DEC_REGEX)) {
			return array(
				'type' => 'decimal',
				'value' => intval($lexer->next()),
			);
		}
		if ($lexer->match(self::OCT_REGEX)) {
			$s = $lexer->next();
			return array(
				'type' => 'octal',
				'value' => octdec($s),
				'original' => $s,
			);
		}
		if ($lexer->match(self::HEX_REGEX)) {
			$s = $lexer->next();
			$r = str_replace(array('0x', '0X', '$'), '', $s);
			return array(
				'type' => 'hex',
				'value' => hexdec($r),
				'original' => $s,
			);
		}
		return false;
	}

	protected function real_constant(JASSLexer $lexer) {
		if ($lexer->match(self::REAL_REGEX)) {
			return array(
				'type' => 'real',
				'value' => $lexer->next(),
			);
		}
		return false;
	}

	protected function bool_constant(JASSLexer $lexer) {
		if (($lexer->peek() == 'true') || ($lexer->peek() == 'false')) {
			return array(
				'type' => 'bool',
				'value' => $lexer->next() == 'true',
			);
		}
		return false;
	}

	protected function string_constant(JASSLexer $lexer) {
		if (substr($lexer->peek(), 0, 1) == '"') {
			return array(
				'type' => 'string',
				'value' => $lexer->next(),
			);
		}
		return false;
	}

	protected function array_ref(JASSLexer $lexer) {
		$lexer->push();
		try {
			if (($id = $this->id($lexer)) === false) {
				return false;
			}
			$lexer->expect('[');
			$index = $this->expr($lexer);
			$lexer->expect(']');
			$lexer->pop();
			return array(
				'type' => 'array_ref',
				'id' => $id,
				'index' => $index,
			);
		} catch (Exception $e) {
			$lexer->rollback();
			return false;
		}
	}

	protected function func_ref(JASSLexer $lexer) {
		if ($lexer->next_is('function')) {
			return array(
				'type' => 'function_ref',
				'id' => $this->id($lexer),
			);
		}
		return false;
	}

	protected function func_call(JASSLexer $lexer) {
		$lexer->push();
		try {
			if (($id = $this->id($lexer)) === false) {
				return false;
			}
			$args = $this->args($lexer);
			$lexer->pop();
			return array(
				'type' => 'call',
				'id' => $id,
				'args' => $args,
			);
		} catch (Exception $e) {
			$lexer->rollback();
			return false;
		}
	}

	protected function args(JASSLexer $lexer) {
		$lexer->expect('(');
		$result = array();
		while(!$lexer->next_is(')')) {
			if (count($result)) {
				$lexer->expect(',');
			}
			$result[] = $this->expr($lexer);
		}
		return $result;
	}

	protected function parenthesis(JASSLexer $lexer) {
		if ($lexer->next_is('(')) {
			$res = $this->expr($lexer);
			$lexer->expect(')');
			return $res;
		}
		return false;
	}

	protected function id(JASSLexer $lexer) {
		if ($lexer->match(self::ID_REGEX)) {
			if (in_array($lexer->peek(), self::$reserved_words)) {
				return false;
			}
			return $lexer->next();
		}
		return false;
	}
}