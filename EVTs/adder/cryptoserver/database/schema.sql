CREATE TABLE users (
    user_id                 VARCHAR(15)                 NOT NULL,
    password                CHAR(40)                    NOT NULL,
    first_name              VARCHAR(20)                 NOT NULL,
    middle_name             VARCHAR(20),
    last_name               VARCHAR(20)                NOT NULL,
    email                   VARCHAR(100),
    salt                    BIGINT          UNSIGNED    NOT NULL,
    deleted                 BOOL                        NOT NULL    DEFAULT 0,
    session_id              CHAR(40),
    session_start           BIGINT          UNSIGNED,
  PRIMARY KEY (user_id),
  UNIQUE KEY (session_id)
);

CREATE TABLE is_authority (
    user_id                 VARCHAR(15)     NOT NULL,
    proc_id                 VARCHAR(36)     NOT NULL,
    number                  SMALLINT        NOT NULL,
    public_key              TEXT            NOT NULL,
    stage                   SMALLINT        NOT NULL,
  PRIMARY KEY (user_id, proc_id)
);

CREATE TABLE auth_poly (
    proc_id                 VARCHAR(36)     NOT NULL,
    auth_src                VARCHAR(15)     NOT NULL,
    auth_dest               VARCHAR(15)     NOT NULL,
    value                   MEDIUMTEXT      NOT NULL,
  PRIMARY KEY (proc_id, auth_src, auth_dest)
);

CREATE TABLE auth_g_values (
    proc_id                 VARCHAR(36)     NOT NULL,
    auth                    VARCHAR(15)     NOT NULL,
    number                  INT             UNSIGNED NOT NULL,
    value                   MEDIUMTEXT      NOT NULL,
  PRIMARY KEY (proc_id, auth, number)
);

CREATE TABLE proc (
    proc_id                     VARCHAR(36)                 NOT NULL,
    title                       VARCHAR(255)                NOT NULL,
    text                        TEXT                        NOT NULL,
    threshold                   SMALLINT        UNSIGNED    NOT NULL,
    create_time                 INT             UNSIGNED    NOT NULL,
    public_key_time             INT             UNSIGNED    NOT NULL,
    polynomial_time             INT             UNSIGNED    NOT NULL,
    secret_key_time             INT             UNSIGNED    NOT NULL,
    vote_time                   INT             UNSIGNED    NOT NULL,
    start_date                  TIMESTAMP                   NOT NULL,
    end_date                    TIMESTAMP                   NOT NULL,
    master_key_length           SMALLINT        UNSIGNED    NOT NULL    DEFAULT 256,
    robustness                  SMALLINT        UNSIGNED    NOT NULL    DEFAULT 2,
    minchoices                  INT             UNSIGNED    NOT NULL,
    maxchoices                  INT             UNSIGNED    NOT NULL,
  PRIMARY KEY (proc_id)
);

CREATE TABLE proc_data (
    proc_id                     VARCHAR(36)                 NOT NULL,
    stage                       TINYINT         UNSIGNED    NOT NULL    DEFAULT 0,
  PRIMARY KEY (proc_id)
);

CREATE TABLE choice (
    proc_id                 VARCHAR(36)     NOT NULL,
    user_id                 VARCHAR(15)     NOT NULL,
    choice                  TEXT            NOT NULL,
    short_hash              TEXT            NOT NULL,
    proof                   TEXT            NOT NULL,
    time_stamp              TIMESTAMP       NOT NULL,
  PRIMARY KEY (proc_id, user_id),
  FOREIGN KEY (proc_id) REFERENCES proc(proc_id),
  FOREIGN KEY (user_id) REFERENCES users(user_id)
);

CREATE TABLE proc_choice (
    proc_id                 VARCHAR(36)     NOT NULL,
    choice_id               BIGINT          NOT NULL,
    text                    TEXT            NOT NULL,
  PRIMARY KEY (proc_id, choice_id),
  FOREIGN KEY (proc_id) REFERENCES proc(proc_id)
);

CREATE TABLE proc_pubkey (
    proc_id                 VARCHAR(36)     NOT NULL,
    public_key              MEDIUMTEXT      NOT NULL,
  PRIMARY KEY (proc_id),
  FOREIGN KEY (proc_id) REFERENCES proc(proc_id)
);

CREATE TABLE proc_masterkey (
    proc_id                 VARCHAR(36)     NOT NULL,
    master_key              MEDIUMTEXT      NOT NULL,
    polynomial              MEDIUMTEXT      NOT NULL,
  PRIMARY KEY (proc_id),
  FOREIGN KEY (proc_id) REFERENCES proc(proc_id)
);

CREATE TABLE cipher_result (
    proc_id                 VARCHAR(36)                     NOT NULL,
    cipher_sum              MEDIUMTEXT                      NOT NULL,
    vote_count              BIGINT          UNSIGNED        NOT NULL,
  PRIMARY KEY (proc_id),
  FOREIGN KEY (proc_id) REFERENCES proc(proc_id)
);

CREATE TABLE preresult (
    proc_id                     VARCHAR(36)     NOT NULL,
    user_id                     VARCHAR(15)     NOT NULL,
    partial_decryption_sum      TEXT            NOT NULL,
  PRIMARY KEY (proc_id, user_id),
  FOREIGN KEY (proc_id) REFERENCES proc(proc_id),
  FOREIGN KEY (user_id) REFERENCES users(user_id)
);

CREATE TABLE pubkey (
    proc_id                 VARCHAR(36)     NOT NULL,
    user_id                 VARCHAR(15)     NOT NULL,
    public_key              TEXT            NOT NULL,
  PRIMARY KEY (proc_id, user_id),
  FOREIGN KEY (proc_id) REFERENCES proc(proc_id),
  FOREIGN KEY (user_id) REFERENCES users(user_id)
);

CREATE TABLE result (
    proc_id                 VARCHAR(36)     NOT NULL,
    choice_id               BIGINT          NOT NULL,
    sum                     INT,
  PRIMARY KEY (proc_id, choice_id),
  FOREIGN KEY (proc_id) REFERENCES proc(proc_id),
  FOREIGN KEY (choice_id) REFERENCES proc_choice(choice_id)
);