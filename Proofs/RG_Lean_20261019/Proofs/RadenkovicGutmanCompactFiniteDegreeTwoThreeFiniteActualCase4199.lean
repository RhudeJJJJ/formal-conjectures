/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons83
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4199 : Family 9 := level9.get ⟨40,by decide⟩
def sourceMap4199 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![2,1,0,11,12,13,14,15,10,9,3,4,5,6,7,8] (sourceLabel 9 2 2 v)
def fusedMap4199 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,8,9,10,11,12,13,14,15,7,1,2,3,4,5,6] (fusedLabel 9 2 2 v)
theorem sourceMap4199_checked : acceptsGraphIso
    (source (graph core4199) (root 9) 2 2) DegreeTwoThreeSpectrum4549.graph sourceMap4199=true := by decide +kernel
theorem fusedMap4199_checked : acceptsGraphIso
    (fused (graph core4199) (root 9) 2 2) DegreeTwoThreeSpectrum3890.graph fusedMap4199=true := by decide +kernel
theorem certified4199 : Certified (graph core4199) (root 9) 2 2 :=
  of_native_maps core4199 DegreeTwoThreeSpectrum4549.graph DegreeTwoThreeSpectrum3890.graph
    sourceMap4199 fusedMap4199 sourceMap4199_checked fusedMap4199_checked
    DegreeTwoThreeFiniteComparisons.comparison4199
#print axioms sourceMap4199_checked
#print axioms fusedMap4199_checked
#print axioms certified4199
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
