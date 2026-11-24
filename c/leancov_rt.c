#include <lean/lean.h>
#include <fcntl.h>
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/resource.h>
#include <sys/stat.h>
#include <unistd.h>

#define LEANCOV_MAGIC "LCOV0001"
#define LEANCOV_HEADER_BYTES 16u

static pthread_once_t g_init_once = PTHREAD_ONCE_INIT;
static uint64_t *g_hits = NULL;
static size_t g_site_count = 0;
static int g_armed = 1;

static void leancov_expand_path(const char *tmpl, char *out, size_t out_sz) {
    size_t j = 0;
    for (size_t i = 0; tmpl[i] != '\0' && j + 1 < out_sz; i++) {
        if (tmpl[i] == '%' && tmpl[i + 1] == 'p') {
            int n = snprintf(out + j, out_sz - j, "%ld", (long)getpid());
            if (n > 0) {
                j += (size_t)n < (out_sz - j) ? (size_t)n : (out_sz - j - 1);
            }
            i++;
        } else {
            out[j++] = tmpl[i];
        }
    }
    out[j] = '\0';
}

static void leancov_init_impl(void) {
    const char *defer_env = getenv("LEAN_COV_DEFER_INIT");
    if (defer_env && defer_env[0] == '1' && defer_env[1] == '\0') {
        __atomic_store_n(&g_armed, 0, __ATOMIC_RELEASE);
    }

    const char *path_env = getenv("LEAN_COV_FILE");
    if (!path_env || path_env[0] == '\0') {
        return;
    }
    char path[4096];
    leancov_expand_path(path_env, path, sizeof(path));

    int fd = open(path, O_RDWR | O_CREAT, 0644);
    if (fd < 0) {
        return;
    }

    size_t sites = 0;
    const char *sites_env = getenv("LEAN_COV_SITES");
    if (sites_env && sites_env[0] != '\0') {
        unsigned long long parsed = strtoull(sites_env, NULL, 10);
        if (parsed > 0 && parsed <= (1ULL << 26)) {
            sites = (size_t)parsed;
        }
    }

    struct stat st;
    if (fstat(fd, &st) != 0) {
        close(fd);
        return;
    }

    if (sites == 0) {
        if (st.st_size >= (off_t)LEANCOV_HEADER_BYTES) {
            uint8_t hdr[LEANCOV_HEADER_BYTES];
            if (pread(fd, hdr, LEANCOV_HEADER_BYTES, 0) == (ssize_t)LEANCOV_HEADER_BYTES &&
                memcmp(hdr, LEANCOV_MAGIC, 8) == 0) {
                uint64_t n = 0;
                memcpy(&n, hdr + 8, 8);
                if (n > 0 && n <= (1ULL << 26)) {
                    sites = (size_t)n;
                }
            }
        }
    }

    if (sites == 0) {
        close(fd);
        return;
    }

    size_t total = LEANCOV_HEADER_BYTES + sites * sizeof(uint64_t);
    if (st.st_size < (off_t)total) {
        if (ftruncate(fd, (off_t)total) != 0) {
            close(fd);
            return;
        }
        uint8_t hdr[LEANCOV_HEADER_BYTES];
        memcpy(hdr, LEANCOV_MAGIC, 8);
        uint64_t n = (uint64_t)sites;
        memcpy(hdr + 8, &n, 8);
        if (pwrite(fd, hdr, LEANCOV_HEADER_BYTES, 0) != (ssize_t)LEANCOV_HEADER_BYTES) {
            close(fd);
            return;
        }
    }

    void *map = mmap(NULL, total, PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0);
    close(fd);
    if (map == MAP_FAILED) {
        return;
    }

    g_hits = (uint64_t *)((uint8_t *)map + LEANCOV_HEADER_BYTES);
    g_site_count = sites;
}

static inline void leancov_bump(size_t site) {
    pthread_once(&g_init_once, leancov_init_impl);
    if (__atomic_load_n(&g_armed, __ATOMIC_ACQUIRE) && g_hits && site < g_site_count) {
        __atomic_fetch_add(&g_hits[site], 1, __ATOMIC_RELAXED);
    }
}

LEAN_EXPORT lean_object *leancov_arm(lean_object *unit) {
    (void)unit;
    pthread_once(&g_init_once, leancov_init_impl);
    __atomic_store_n(&g_armed, 1, __ATOMIC_RELEASE);
    return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_object *leancov_hit(size_t site, lean_object *f) {
    leancov_bump(site);
    return lean_apply_1(f, lean_box(0));
}

LEAN_EXPORT uint8_t leancov_cond(size_t t_site, size_t f_site, uint8_t b) {
    leancov_bump(b ? t_site : f_site);
    return b;
}

LEAN_EXPORT lean_object *leancov_pass(size_t site, lean_object *x) {
    leancov_bump(site);
    return x;
}

LEAN_EXPORT uint8_t leancov_mark(size_t site) {
    leancov_bump(site);
    return 1;
}

LEAN_EXPORT lean_object *leancov_raise_stack(lean_object *unit) {
    (void)unit;
    struct rlimit rl;
    if (getrlimit(RLIMIT_STACK, &rl) == 0) {
        rlim_t target = (rlim_t)(64ULL * 1024ULL * 1024ULL);
        if (rl.rlim_max != RLIM_INFINITY && target > rl.rlim_max) {
            target = rl.rlim_max;
        }
        if (rl.rlim_cur != RLIM_INFINITY && rl.rlim_cur < target) {
            rl.rlim_cur = target;
            if (setrlimit(RLIMIT_STACK, &rl) != 0) {}
        }
    }
    return lean_io_result_mk_ok(lean_box(0));
}
