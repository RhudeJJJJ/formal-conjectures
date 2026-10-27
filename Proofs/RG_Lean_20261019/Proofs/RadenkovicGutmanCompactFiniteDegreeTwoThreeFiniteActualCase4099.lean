/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons81
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4099 : Family 8 := level8.get ⟨19,by decide⟩
def sourceMap4099 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,6,0,1,2,3,4,5,14,8,9,10,11,12,13] (sourceLabel 8 2 2 v)
def fusedMap4099 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,14,8,9,10,11,12,13] (fusedLabel 8 2 2 v)
theorem sourceMap4099_checked : acceptsGraphIso
    (source (graph core4099) (root 8) 2 2) DegreeTwoThreeSpectrum2796.graph sourceMap4099=true := by decide +kernel
theorem fusedMap4099_checked : acceptsGraphIso
    (fused (graph core4099) (root 8) 2 2) DegreeTwoThreeSpectrum2380.graph fusedMap4099=true := by decide +kernel
theorem certified4099 : Certified (graph core4099) (root 8) 2 2 :=
  of_native_maps core4099 DegreeTwoThreeSpectrum2796.graph DegreeTwoThreeSpectrum2380.graph
    sourceMap4099 fusedMap4099 sourceMap4099_checked fusedMap4099_checked
    DegreeTwoThreeFiniteComparisons.comparison4099
#print axioms sourceMap4099_checked
#print axioms fusedMap4099_checked
#print axioms certified4099
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
