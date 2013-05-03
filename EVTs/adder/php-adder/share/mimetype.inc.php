<?php
$has_xml = false;

if (isset($_SERVER['HTTP_ACCEPT'])) {
    if (preg_match('/application\/xhtml\+xml(;q=(0(\.\d{1,3})?|1(\.0{1,3})?))?/', $_SERVER['HTTP_ACCEPT'], $matches)) {
        $has_xml = true;
        $xhtml_q = isset($matches[1]) ? $matches[1] : 0;

        if ($xhtml_q > 0 && preg_match('/text\/html(;q=(0(\.\d{1,3})?|1(\.0{1,3})?))?/', $_SERVER['HTTP_ACCEPT'], $matches)) {
            $html_q = $matches[1];

            if ($xhtml_q < $html_q) {
                $has_xml = false;
            }
        }
    }
}

if ($has_xml) {
    header('Content-Type: application/xhtml+xml');
} else {
    header('Content-Type: text/html;charset=utf-8');
}

header('Content-Script-Type: text/javascript');
header('Vary: Accept');
