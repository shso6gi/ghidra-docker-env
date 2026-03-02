# -*- coding: utf-8 -*-
"""アーキテクチャ検出モジュール"""

from typing import Optional


class ArchitectureDetector:
    """アーキテクチャを検出するクラス"""
    
    def __init__(self, debug: bool = False):
        self.debug = debug
    
    def _debug_print(self, msg: str):
        if self.debug:
            print(f"[ArchitectureDetector] {msg}")
    
    def is_mips64(self, program) -> bool:
        """
        MIPS64アーキテクチャかどうかを判定
        
        Args:
            program: Ghidra Program オブジェクト
        
        Returns:
            True: MIPS64 である
            False: MIPS64 でない
        """
        try:
            lang = program.getLanguage()
            lang_id = lang.getLanguageID()
            lang_id_str = str(lang_id)
            
            # LanguageID の文字列表現: "MIPS:BE:64:default", "MIPS:LE:64:64-32addr" 等
            if "MIPS" in lang_id_str.upper() and "64" in lang_id_str:
                self._debug_print(f"Detected MIPS64: LanguageID = {lang_id_str}")
                return True
            
            # フォールバック: プロセッサ名とポインタサイズで判定
            processor = lang.getProcessor()
            processor_str = str(processor)
            if "MIPS" in processor_str.upper():
                pointer_size = program.getDefaultPointerSize()
                if pointer_size == 8:
                    self._debug_print(
                        f"Detected MIPS64: Processor = {processor_str}, "
                        f"PointerSize = {pointer_size}"
                    )
                    return True
        except Exception as e:
            self._debug_print(f"Error detecting MIPS64: {e}")
        
        return False
    
    def get_architecture_info(self, program) -> dict:
        """アーキテクチャ情報を取得"""
        info = {
            "is_mips64": False,
            "processor": "unknown",
            "pointer_size": 0,
            "language_id": "unknown"
        }
        
        try:
            lang = program.getLanguage()
            info["language_id"] = str(lang.getLanguageID())
            info["processor"] = str(lang.getProcessor())
            info["pointer_size"] = program.getDefaultPointerSize()
            info["is_mips64"] = self.is_mips64(program)
        except Exception as e:
            self._debug_print(f"Error getting architecture info: {e}")
        
        return info