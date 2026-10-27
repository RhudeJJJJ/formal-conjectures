/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons85
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4263 : Family 9 := level9.get ⟨253,by decide⟩
def sourceMap4263 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,9,10,11,12,13,14,15,8,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap4263 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4263_checked : acceptsGraphIso
    (source (graph core4263) (root 9) 2 2) DegreeTwoThreeSpectrum4883.graph sourceMap4263=true := by decide +kernel
theorem fusedMap4263_checked : acceptsGraphIso
    (fused (graph core4263) (root 9) 2 2) DegreeTwoThreeSpectrum4061.graph fusedMap4263=true := by decide +kernel
theorem certified4263 : Certified (graph core4263) (root 9) 2 2 :=
  of_native_maps core4263 DegreeTwoThreeSpectrum4883.graph DegreeTwoThreeSpectrum4061.graph
    sourceMap4263 fusedMap4263 sourceMap4263_checked fusedMap4263_checked
    DegreeTwoThreeFiniteComparisons.comparison4263
#print axioms sourceMap4263_checked
#print axioms fusedMap4263_checked
#print axioms certified4263
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
