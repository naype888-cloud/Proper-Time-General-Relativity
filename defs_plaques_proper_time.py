def PLAQUES(title, sub, label, foot, eq, txt):
    return {
        "plaque_master_proper_time_gr": [
            title("LE TEMPS PROPRE ENGENDRE LA RELATIVITÉ GÉNÉRALE"),
            sub(r"Formalisation par Eduardo Nava Hernández \& José Arturo Nava-Hernández", "gold"),
            sub(r"Géométrie discrète · défaut quantique de Robertson–Schrödinger · courbure métrique dynamique"),
            r"\vspace{20bp}",
            eq(r"\tau_{\mathrm{step}}(t, N) = \dfrac{1}{2|t|\cos\big(\frac{\pi}{N+1}\big)} > 0 \;\Longrightarrow\; m > 0 \;\Longrightarrow\; \alpha_G = \dfrac{G m^2}{\hbar c} > 0", "green", 64),
            label(r"1 · L'Annulation de l'échelle de réseau : « t = N pas »", "gold"),
            eq(r"\dfrac{a}{v_{\mathrm{max}}(t, a, N)} = \tau_{\mathrm{step}}(t, N) = \dfrac{1}{2|t|\cos\big(\frac{\pi}{N+1}\big)}"),
            label("2 · L'Équivalence de Mandelstam–Tamm et du saut quantique", "blue"),
            eq(r"\Delta E_{\mathrm{MT}} = \dfrac{\hbar}{2\,\tau_{\mathrm{step}}(t, N)} = \hbar\,|t|\,\cos\Big(\dfrac{\pi}{N+1}\Big) = E_{\mathrm{hopping}}(t, N)"),
            label("3 · La Rupture de saturation en dimension 4", "violet"),
            eq(r"d \le 3 \;\Longrightarrow\; C_M(d) = 0 \quad (\text{phase luminale sans masse, } d\tau = 0)"),
            eq(r"d = 4 \;\Longrightarrow\; C_M(4) = \dfrac{94 - 42\sqrt{5}}{5} \approx 0{,}017029 > 0 \quad (d\tau > 0)"),
            label("4 · L'Émergence inéluctable de la courbure d'Einstein", "green"),
            eq(r"g_{00}(x) = -\Big(1 + \dfrac{2\Phi(x)}{c^2}\Big) \;\Longrightarrow\; R^\rho_{\ \sigma\mu\nu} \neq 0 \;\Longrightarrow\; G_{\mu\nu} = \dfrac{8\pi G}{c^4} T_{\mu\nu}"),
            foot(r"VÉRIFIÉ ET CERTIFIÉ PAR LE NOYAU LEAN 4 · 0 SORRY · BASE STANDARD \texttt{[propext, Classical.choice, Quot.sound]}"),
        ],
        "plaque_axiome_fondateur": [
            r"\vspace{14bp}",
            eq(r"\tau_{\mathrm{step}}(t, N) > 0 \;\iff\; m > 0 \;\iff\; g_{\mu\nu}(x) \neq \eta_{\mu\nu}", "gold", 74),
        ],
        "plaque_annulation_reseau": [
            r"\vspace{10bp}",
            eq(r"\dfrac{a}{v_{\mathrm{max}}(t, a, N)} = \dfrac{a}{2|a t|\cos\big(\frac{\pi}{N+1}\big)} = \dfrac{1}{2|t|\cos\big(\frac{\pi}{N+1}\big)} = \tau_{\mathrm{step}}(t, N)", "green", 66),
        ],
        "plaque_mandelstam_tamm_hopping": [
            r"\vspace{10bp}",
            eq(r"\dfrac{\hbar}{2\,\tau_{\mathrm{step}}(t, N)} = \hbar\,|t|\,\cos\Big(\dfrac{\pi}{N+1}\Big) = E_{\mathrm{hopping}}(t, N)", "blue", 68),
        ],
        "plaque_courbure_einstein": [
            r"\vspace{10bp}",
            eq(r"\alpha_G \equiv \dfrac{G\,m^2}{\hbar\,c} = \dfrac{\mathrm{scale}^2\,C_M(4)}{M_P^2} > 0 \;\Longrightarrow\; G_{\mu\nu} = \dfrac{8\pi G}{c^4}\,T_{\mu\nu}", "gold", 68),
        ],
    }
