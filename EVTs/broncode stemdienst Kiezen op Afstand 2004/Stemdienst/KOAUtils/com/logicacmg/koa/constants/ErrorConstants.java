/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.constants.ErrorConstants.java
  *
  * -----------------------------------------------------------------------
  * 
  *  (c) 2003  Ministerie van Binnenlandse Zaken en Koninkrijkrelaties
  *
  *  Project		: Kiezen Op Afstand (KOA)
  *  Project Number	: ECF-2651
  *  
  *  History:
  *  Version	Date		Name		Reason
  * ---------------------------------------------------------
  *  0.1		02-05-2003	MKu			First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.constants;
/**
 * All the error codes used for mapping the
 * exception that will be thrown and the error messages.
 * 
 * @author KuijerM
 * 
 */
public class ErrorConstants
{
	/**
	 * Private error constants constructor
	 * to prevent the class to be initialized.
	 * 
	 */
	private ErrorConstants()
	{
	}
	public final static String ERR_REPORT_GENERATE_TRANSFORM_CONFIG =
		"koaerr_report_generate_transform_config";
	public final static String ERR_REPORT_GENERATE_TRANSFORM =
		"koaerr_report_generate_transform";
	public final static String ERR_REPORT_GENERATE_DEFAULT =
		"koaerr_report_generate_default";
	public final static String ERR_REPORTS_DB_GLOBAL_HEADER =
		"koaerr_reports_db_global_header";
	public final static String ERR_GENERATE_REPORT = "koaerr_generate_report";
	public final static String ERR_CLIENT_ADD_SUBSCRIPTION =
		"koaerr_client_add_subscription";
	public final static String ERR_CLIENT_REMOVE_SUBSCRIPTION =
		"koaerr_client_remove_subscription";
	public final static String ERR_READER_INIT = "koaerr_reader_init";
	public final static String ERR_READER_GET_MORE = "koaerr_reader_get_more";
	public final static String ERR_SECUR_DECRYPT = "koaerr_secur_decrypt";
	public final static String ERR_SECUR_ENCRYPT = "koaerr_secur_encrypt";
	public final static String ERR_FILE_UPLOAD = "koaerr_file_upload";
	public final static String ERR_SAX_PARSE_EXCEPTION =
		"koaerr_sax_parse_exception";
	public final static String ERR_SAX_EXCEPTION = "koaerr_sax_exception";
	public final static String ERR_NUMBER_FORMAT = "koaerr_number_format";
	public final static String ERR_NULL_POINTER = "koaerr_null_pointer";
	public final static String ERR_CONVERTOR_CONVERT_BYTE_TO_OBJECT =
		"koaerr_convertor_convert_byte_to_object";
	public final static String ERR_CONVERTOR_CONVERT_OBJECT_TO_BYTE =
		"koaerr_convertor_convert_object_to_byte";
	public final static String ERR_CONTROL_CLIENT_DEFAULT =
		"koaerr_control_client_default";
	public final static String ERR_SQL = "koaerr_sql";
	public final static String ERR_REMOVE_ENTITY = "koaerr_remove_entity";
	public final static String ERR_CLOSE_STREAM = "koaerr_close_stream";
	public final static String ERR_COMM_VSL_TO_TSM = "koaerr_comm_vsl_to_tsm";
	public final static String ERR_COMM_TSM_TO_VSL = "koaerr_comm_tsm_to_vsl";
	public final static String ERR_SCHEDULER_JOBCONTEXT =
		"koaerr_scheduler_jobcontext";
	public final static String ERR_SCHEDULER_EXECUTE_SCHEDULED_JOB =
		"koaerr_scheduler_execute_scheduled_job";
	public final static String ERR_SCHEDULER_CREATE_SUCCESSOR_JOB =
		"koaerr_scheduler_create_successor_job";
	public final static String ERR_REPORT_DATA_INIT = "koaerr_report_data_init";

	public final static String ERR_DIFF_FINGERPRINTS =
		"koaerr_fingerprints_compare_dif";
	public final static String ERR_PARSE_PUB_PRIVKEY =
		"koaerr_key_upload_invalid_key";
	public final static String INFO_CHANGESTATE_START =
		"koainfo_change_state_error_log_message";

	public final static String ERR_IMPORT_INCORRECT_ACTION =
		"err_import_incorrect_action";
	public final static String ERR_LOAD_OBJECTS =
		"koaerr_scheduler_loadobjects";
	public final static String ERR_LOAD_OBJECTS_PROPS =
		"koaerr_scheduler_loadobjectsprops";
	public final static String ERR_BLOBREPORT_CLOSE = "koaerr_blobreport_close";
	public final static String ERR_COUNTERREADER_CLOSE =
		"koaerr_counterreader_close";
	public final static String ERR_WEB_SUBSCRIBE = "koaerr_web_subscribe";
	public final static String ERR_INIT_RANDOM = "koaerr_init_random";
	public final static String ERR_AUDIT_INSERT = "koaerr_audit_insert";
	public final static String ERR_EMPTY_KR = "koaerr_empty_kr";
	public final static String ERR_NAMING = "koaerr_naming_exception";
	public final static String ERR_CREATE = "koaerr_create_exception";
	public final static String ERR_REMOTE = "koaerr_remote_exception";
	public final static String ERR_IO = "koaerr_io_exception";
	public final static String ERR_FINDER = "koaerr_finder_exception";
	public final static String ERR_RESULT_BLOCK_SYSTEM =
		"koaerr_blocking_system";
	public final static String DEFAULT = "default";
	public final static String CONTROLLER_BEAN_COUNT_VOTE_ESB =
		"controller_bean_count_votes_on_esb";
	public final static String DBUTILS_GET_CONNECTION =
		"dbutils_get_connection";
	public final static String DBUTILS_EXEC_QUERY = "dbutils_execute_query";
	public final static String DBUTILS_NO_DATASOURCE = "dbutils_no_datasource";
	public final static String CONTROLLER_GETSTATE = "controller_get_state";
	public final static String CONTROLLER_SAVESTATE = "controller_save_state";
	public final static String CONTROLLER_GET_STATE_ENTITY =
		"controller_get_state_entity";
	public final static String CONTROLLER_CREATE_STATE_ENTITY =
		"controller_create_state_entity";
	public final static String CONTROLLER_OPEN_ESB = "controller_open_esb";
	public final static String CONTROLLER_DB_GET_COUNTERS =
		"controller_db_get_counters";
	public final static String CONTROLLER_DB_GET_GROUP_ID =
		"controller_db_getgroupid";
	public final static String CONTROLLER_DB_INSERT_COUNTERS =
		"controller_db_insert_counters";
	public final static String CONTROLLER_DB_GET_FREE_ID =
		"controller_db_get_free_id";
	public final static String CONTROLLER_DB_CHECK_INTERNAL_ROW =
		"controller_db_check_internal_row";
	public final static String CONTROLLER_DB_SUBSCRIBE =
		"controller_db_subscribe";
	public final static String CONTROLLER_DB_UNSUBSCRIBE =
		"controller_db_unsubscribe";
	public final static String CONTROLLER_DB_COUNT_SUBSCRIBERS =
		"controller_db_count_subscribers";
	public final static String CONTROLLER_DB_GET_SUBSCRIBERS =
		"controller_db_get_subscribers";
	public final static String CONTROLLER_DB_LOAD_PUBLICKEY =
		"controller_db_load_public_key";
	public final static String CONTROLLER_DB_SAVE_PUBLICKEY =
		"controller_db_save_public_key";
	public final static String CONTROLLER_DB_GET_WEB_COUNTER =
		"controller_db_get_web_counter";
	public final static String CONTROLLER_DB_GET_PINCODE =
		"controller_db_get_pincode";
	public final static String SCHEDULER_CONFIG_JOB = "scheduler_config_job";
	public final static String SCHEDULER_RESCHEDULE_JOB =
		"scheduler_reschedule_job";
	public final static String SCHEDULER_REMOVE_JOB = "scheduler_remove_job";
	public final static String SCHEDULER_JOBTARGET_EXECUTE =
		"scheduler_jobtarget_execute";
	public final static String SCHEDULER_CREATE_SUCCESSOR =
		"scheduler_create_successor";
	public final static String SUBSCRIPTIONMANAGER_ADD_SUBSCRIBER =
		"subscriptionmanager_add_subscriber";
	public final static String SUBSCRIPTIONMANAGER_REMOVE_SUBSCRIBER =
		"subscriptionmanager_remove_subscriber";
	public final static String SUBSCRIPTIONMANAGER_ESB_SUBSCRIBER =
		"subscriptionmanager_esb_subscriber";
	public final static String SUBSCRIPTIONMANAGER_KR_SUBSCRIBER =
		"subscriptionmanager_kr_subscriber";
	public final static String CLIENTMANAGER_SUBSCRIBE =
		"clientmanager_subscribe";
	public final static String CLIENTMANAGER_UNSUBSCRIBE =
		"clientmanager_unsubscribe";
	public final static String CLIENTMANAGER_GETSTATE =
		"clientmanager_getstate";
	public final static String CONTROL_CLIENT_SUBSCRIBE =
		"control_client_subscribe";
	public final static String CONTROL_CLIENT_UNSUBSCRIBE =
		"control_client_unsubscribe";
	public final static String CONTROL_CLIENT_REGISTER =
		"control_client_register";
	public final static String CONTROL_CLIENT_SUBSCRIPTION_NOTIFY =
		"control_client_subscription_notify";
	public final static String CONTROL_CLIENT_SUBSCRIPTION_COLLECTCOUNTERS =
		"control_client_subscription_collectcounters";
	public final static String KR_CLIENT_SUBSCRIPTION_NOTIFY =
		"kr_client_subscription_notify";
	public final static String KR_CLIENT_SUBSCRIPTION_COLLECTCOUNTERS =
		"kr_client_subscription_collectcounters";
	public final static String ESB_CLIENT_SUBSCRIPTION_NOTIFY =
		"esb_client_subscription_notify";
	public final static String ESB_CLIENT_SUBSCRIPTION_COLLECTCOUNTERS =
		"esb_client_subscription_collectcounters";
	public final static String SECURITY_KEYPAIR_GENERATE =
		"security_keypair_generate";
	public final static String SECURITY_KEYPAIR_DECRYPT =
		"security_keypair_decrypt";
	public final static String SECURITY_KEYPAIR_ENCRYPT_PUBLIC =
		"security_keypair_encrypt_public";
	public final static String SECURITY_KEYPAIR_ENCRYPT_PRIVATE =
		"security_keypair_encrypt_private";
	public final static String SECURITY_KEYPAIR_ENCRYPT =
		"security_keypair_encrypt";
	public final static String SECURITY_PUBLICKEY_LOAD =
		"security_publickey_load";
	public final static String SECURITY_HASHING_PINCODE =
		"security_hashing_pincode";
	public final static String COMMAND_CHANGE_STATE_EXEC =
		"command_change_state_execute";
	public final static String COMMAND_GETCOUNTERS_EXEC =
		"command_getcounters_execute";
	public final static String COMMAND_GETSTATE_EXEC =
		"command_getstate_execute";
	public final static String COMMAND_INITIALIZE_EXEC =
		"command_initialize_execute";
	public final static String COMMAND_INITIALIZE_INIT =
		"command_initialize_init";
	public final static String COMMAND_GET_FILEITEM = "command_get_fileitem";
	public final static String COMMAND_SAVECOUNTERS_EXEC =
		"command_savecounters_execute";
	public final static String COMMAND_COUNTVOTE_INIT =
		"command_countvote_init";
	public final static String COMMAND_COUNTVOTE_EXEC =
		"command_countvote_execute";
	public final static String COMMAND_PREPARECOUNTVOTE_EXEC =
		"command_preparecountvote_execute";
	public final static String COMMAND_OPEN_EXEC = "command_open_execute";
	public final static String COMMAND_SUSPEND_EXEC = "command_suspend_execute";
	public final static String COMMAND_CLOSE_EXEC = "command_close_execute";
	public final static String COMMAND_PREPARE_EXEC = "command_prepare_execute";
	public final static String CONVERTOR_BYTE_OBJ =
		"convertor_bytearray_to_object";
	public final static String CONVERTOR_OBJ_BYTE =
		"convertor_object_to_bytearray";
	public final static String CONVERTOR_PRIV_KEY = "convertor_private_key";
	public final static String CONVERTOR_PUBL_KEY = "convertor_public_key";
	public final static String JNDI_PROPS_LOAD = "jndiprops_load";
	public final static String JNDI_PROPS_NOT_FOUND =
		"jndiprops_prop_not_found";
	public final static String FUNC_PROPS_LOAD = "funcprops_load";
	public final static String FUNC_PROPS_NOT_FOUND =
		"funcprops_prop_not_found";
	public final static String TECHN_PROPS_LOAD = "technprops_load";
	public final static String TECHN_PROPS_NOT_FOUND =
		"technprops_prop_not_found";
	public final static String PROPS_NO_INTEGER = "technprops_prop_no_integer";
	public final static String AUDITLOG_LOAD = "auditlog_load";
	public final static String COUNTERKEYS_LOAD = "counterkeys_load";
	public final static String COUNTERKEYS_NOT_FOUND =
		"counterkeys_prop_not_found";
	public final static String ESB_ERROR = "esb_err";
	public final static String ESB_TELSTEMMEN_ERR = "esb_telstemmen";
	public final static String KR_ERROR = "kr_error";
	public final static String KR_STATE_TRANSITION_ERROR =
		"error_KR_state_transition";
	public final static String VERIFY_STEM_CODE_ERR = "VERIFY_STEM_CODE_ERR";
	public final static String VERIFY_STEM_CODE_NUMERIC_ERR =
		"VERIFY_STEM_CODE_NUMERIC_ERR";
	public final static String CUSTOM_REGISTRY = "custom_registry";
	public final static String ENCRYPTION_ERROR = "ENCRYPTION_ERROR";
	public final static String DECRYPTION_ERROR = "DECRYPTION_ERROR";
	public final static String KLB_GET_KIESKRING_ERROR =
		"KLB_GET_KIESKRING_ERROR";
	public final static String KLB_KANDIDAAT_ERR = "kieslijst_kandidaat_err";
	public final static String KLB_KANDIDATEN_ERR = "kieslijst_kandidaten_err";
	public final static String VERIFY_CANDIDATE_ERR = "VERIFY_CANDIDATE_ERR";
	// RB:10-09-2003
	public final static String VERIFY_CANDIDATE_CODE_ERR =
		"VERIFY_CANDIDATE_CODE_ERR";
	public final static String VERIFY_CANDIDATE_CODE_NUMERIC_ERR =
		"VERIFY_CANDIDATE_CODE_NUMERIC_ERR";
	public final static String VERIFY_CANDIDATE_ATTEMPTS_EXCEEDED =
		"VERIFY_CANDIDATE_ATTEMPTS_EXCEEDED";
	public final static String KLB_PARTIJEN_ERR = "kieslijst_partijen_err";
	public final static String VOTER_EXECUTE_VOTE_ERROR =
		"voter_execute_vote_error";
	public final static String ERR_INVALID_CREDENTIALS =
		"err_invalid_credentials";
	public final static String ERR_ALREADY_VOTED = "err_already_voted";
	public final static String ERR_NO_AUTORISATION = "err_no_autorisation";
	public final static String NO_CREDENTIALS = "no_credentials";
	public final static String ERR_KIEZER_ERR = "err_kiezer_err";
	public final static String ERR_ACCOUNT_TIMELOCK = "err_account_timelock";
	public final static String ERR_KIEZER_DELETED = "err_kiezer_deleted";
	public final static String ERR_ELECTION_NOT_YET_OPEN =
		"err_election_not_yet_open";
	public final static String ERR_ELECTION_BLOCKED = "err_election_blocked";
	public final static String ERR_ELECTION_SUSPENDED =
		"err_election_suspended";
	public final static String ERR_ELECTION_CLOSED = "err_election_closed";
	public final static String ERR_CANDIDATE_NOT_FOUND =
		"err_candidate_not_found";
	public final static String ERR_CANDIDATE_ERR = "err_candidate_err";
	public final static String ESB_FINGERPRINT_ERROR = "esb_fingerprint_err";
	public final static String DYNAMIC_KR_FINGERPRINT_ERROR =
		"dynamic_kr_fingerprint_err";
	public final static String STATIC_KR_FINGERPRINT_ERROR =
		"static_kr_fingerprint_err";
	public final static String GENERIC_TECHNICAL_ERR = "technical_err";
	public final static String REPORT_NO_SUCH_REPORT = "report_no_such_report";
	public final static String REPORT_PRELOAD_REPORTS =
		"reports_preload_reports";
	public final static String REPORTDATA_GET_REPORTDATA =
		"report_data_get_reportdata";
	public final static String REPORTDATA_INIT = "report_data_init";
	public final static String REPORT_DATA_COMMAND = "report_data_command";
	public final static String REPORT_COMMAND = "report_command";
	public final static String REPORT_GLOBAL_HEADER =
		"report_get_global_header";
	public final static String REPORT_VERKIEZINGSUITSLAG_DEFAULT =
		"report_verkiezingsuitslag_default";
	public final static String REPORT_VERKIEZINGSUITSLAG_MEER_UITSLAGEN =
		"report_verkiezingsuitslag_meer_uitslagen";
	public final static String REPORT_PROCESVERBAAL_DEFAULT =
		"report_procesverbaal_default";
	public final static String REPORT_EXPORT_DEFAULT = "report_export_default";
	public final static String REPORT_COUNTER_REPORT_INIT =
		"report_counter_report_init";
	public final static String REPORT_PDF_NO_SOURCE = "report_pdf_no_source";
	public final static String REPORT_PDF_GENERATE = "report_pdf_generate";
	public final static String REPORT_XML_NO_SOURCE = "report_xml_no_source";
	public final static String REPORT_XML_GENERATE = "report_xml_generate";
	public final static String REPORT_XSL_NO_SOURCE = "report_xsl_no_source";
	public final static String REPORT_XSL_GENERATE = "report_xsl_generate";
	public final static String STEMPROCES_ERROR = "stemproces_error";
	public final static String AUDIT_LOG_INSERT = "audit_log_insert";
	public final static String VCCOMMAND_ERROR = "vccommand_error";
	public final static String KIEZER_INVALID_CREDENTIALS =
		"kiezer_invalid_credentials";
	public final static String MAX_ATTEMPTS_EXCEEDED = "MAX_ATTEMPTS_EXCEEDED";
	public final static String VALIDATE_PUBLIC_KEY = "validate_public_key";
	public final static String VALIDATE_PRIVATE_KEY = "validate_private_key";
	public final static String CMD_COMPARE_FINGERPRINTS_ERR =
		"cmd_compare_fingerprints_err";
	public final static String COUNTER_XML_READER_VALIDATE_DATES =
		"counter_xml_reader_validate_dates";
	public final static String ESB_NOT_EMPTY_DURING_INIT =
		"esb_not_empty_during_initialize";
	public final static String CHANGE_STATE_MESSAGE_ESB_FINGERPRINT_ERR =
		"change_state_message_esb_fingerprint_err";
	public final static String CHANGE_STATE_MESSAGE_KR_DYN_FINGERPRINT_ERR =
		"change_state_message_kr_dyn_fingerprint_err";
	public final static String CHANGE_STATE_MESSAGE_KR_STAT_FINGERPRINT_ERR =
		"change_state_message_kr_stat_fingerprint_err";
	public final static String CHANGE_STATE_BLOCKING = "change_state_blocking";
	public final static String CHANGE_STATE_AUDIT_START_CHANGE =
		"change_state_audit_start_change";
	public final static String CHANGE_STATE_AUDIT_FIND_SUBSCRIBERS =
		"change_state_audit_find_subscribers";
	public final static String CHANGE_STATE_AUDIT_CHANGE_STATE_SUCCEFUL =
		"change_state_audit_change_state_succesful";
	public final static String CHANGE_STATE_AUDIT_CHANGE_STATE_PARTLY =
		"change_state_audit_change_state_partly";
	public final static String CHANGE_STATE_AUDIT_CHANGE_STATE_ERROR_NO_CHANGE =
		"change_state_audit_change_state_error_no_change";
	public final static String CHANGE_STATE_AUDIT_CHANGE_STATE_ERROR_CHANGE =
		"change_state_audit_change_state_error_change";
	public final static String CHANGE_STATE_AUDIT_SAVE_STATE =
		"change_state_audit_save_state";
	public final static String CHANGE_STATE_AUDIT_SAVE_STATE_ERROR =
		"change_state_audit_save_state_error";
	public final static String CHANGE_STATE_AUDIT_SAVE_STATE_UNKNOWN_ERROR =
		"change_state_audit_save_state_unknown_error";
	public final static String CHANGE_STATE_AUDIT_INVALID_FINGERPRINTS =
		"change_state_audit_invalid_fingerprints";
	public final static String CHANGE_STATE_AUDIT_NOTIFY_COMPONENT_OK =
		"change_state_audit_notify_component_ok";
	public final static String CHANGE_STATE_AUDIT_NOTIFY_COMPONENT_ERROR =
		"change_state_audit_notify_component_error";
	public final static String CHANGE_STATE_CHECK_CANDIDATES_OK =
		"change_state_check_candidates_ok";
	public final static String CHANGE_STATE_CHECK_CANDIDATES_ERROR =
		"change_state_check_candidates_error";
	public final static String CHANGE_STATE_AUDIT_ESB_NOT_EMPTY =
		"change_state_audit_esb_not_empty";
	public final static String CHANGE_STATE_AUDIT_ESB_EMPTY =
		"change_state_audit_esb_empty";
	public final static String FINGERPRINT_CREATE_KIESLIJST_FINGERPRINTS =
		"fingerprint_kieslijst_create_fingerprints";
	public final static String FINGERPRINT_KIESLIJST_CREATE_SINGLE_FINGERPRINT =
		"fingerprint_kieslijst_create_single_fingerprint";
	public final static String FINGERPRINT_KIESLIJST_COMPARE_FINGERPRINTS =
		"fingerprint_kieslijst_compare_fingerprints";
	public final static String FINGERPRINT_KIESLIJST_COMPARE_FINGERPRINT_EQUAL =
		"fingerprint_kieslijst_compare_fingerprint_equal";
	public final static String FINGERPRINT_KIESLIJST_COMPARE_FINGERPRINT_DIFFERENT =
		"fingerprint_kieslijst_compare_fingerprint_different";
	public final static String VOTER_TICKET_EXPIRED = "voter_ticket_expired";
	public final static String CHANGE_STATE_BLOCKED_RETURN_MESSAGE =
		"change_state_blocked_return_message";
	public final static String ERR_BLOCK_SYSTEM = "err_result_is_block_system";
	public final static String WRONG_FINGERPRINT_TYPE =
		"wrong_fingerprint_type";
	public final static String IMPORT_KIESLIJST_START =
		"import_kieslijst_start";
	public final static String IMPORT_KIESLIJST_SUCCESS =
		"import_kieslijst_success";
	public final static String IMPORT_KIESLIJST_FAILURE =
		"import_kieslijst_failure";
	public final static String IMPORT_KIESREGISTER_START =
		"import_kiesregister_start";
	public final static String IMPORT_KIESREGISTER_SUCCESS =
		"import_kiesregister_success";
	public final static String IMPORT_KIESREGISTER_FAILURE =
		"import_kiesregister_failure";
	public final static String DELETE_KIESREGISTER_SUCCESS =
		"delete_kiesregister_success";
	public final static String UNABLE_TO_START_BACKUP_SCRIPT =
		"unable_to_start_backup_script";
	public final static String CREATE_BACKUP_OK = "create_backup_ok";
	public final static String CREATE_BACKUP_ERROR = "create_backup_error";
	public final static String CREATE_FS_BACKUP_OK = "create_fs_backup_ok";
	public final static String CREATE_FS_BACKUP_ERROR =
		"create_fs_backup_error";
	public final static String CREATE_TAPE_BACKUP_OK = "create_tape_backup_ok";
	public final static String CREATE_TAPE_BACKUP_ERROR =
		"create_tape_backup_error";
	public final static String CHECK_TAPE_BACKUP = "check_tape_backup";
	public final static String CHANGE_STATE_RESULT_MESSAGE_SUCCESFUL =
		"change_state_webresult_change_state_succesful";
	public final static String CHANGE_STATE_RESULT_MESSAGE_PARTLY =
		"change_state_webresult_change_state_partly";
	public final static String CHANGE_STATE_RESULT_MESSAGE_ERROR_NO_CHANGE =
		"change_state_webresult_change_state_error_no_change";
	public final static String CHANGE_STATE_RESULT_MESSAGE_ERROR_CHANGE =
		"change_state_webresult_change_state_error_change";
	public final static String XML_DECRYPT_VOTES_WRITER_INIT =
		"xml_decrypt_votes_writer_init";
}