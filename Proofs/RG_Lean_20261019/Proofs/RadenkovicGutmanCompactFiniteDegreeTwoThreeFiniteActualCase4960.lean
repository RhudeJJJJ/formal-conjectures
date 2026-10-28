/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons99
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4960 : Family 10 := level10.get ⟨1528,by decide⟩
def sourceMap4960 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4960 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4960_checked : acceptsGraphIso
    (source (graph core4960) (root 10) 2 2) DegreeTwoThreeSpectrum7561.graph sourceMap4960=true := by decide +kernel
theorem fusedMap4960_checked : acceptsGraphIso
    (fused (graph core4960) (root 10) 2 2) DegreeTwoThreeSpectrum5964.graph fusedMap4960=true := by decide +kernel
theorem certified4960 : Certified (graph core4960) (root 10) 2 2 :=
  of_native_maps core4960 DegreeTwoThreeSpectrum7561.graph DegreeTwoThreeSpectrum5964.graph
    sourceMap4960 fusedMap4960 sourceMap4960_checked fusedMap4960_checked
    DegreeTwoThreeFiniteComparisons.comparison4960
#print axioms sourceMap4960_checked
#print axioms fusedMap4960_checked
#print axioms certified4960
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
