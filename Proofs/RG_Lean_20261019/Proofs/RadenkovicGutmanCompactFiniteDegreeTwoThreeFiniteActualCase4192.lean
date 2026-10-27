/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons83
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4192 : Family 8 := level8.get ⟨271,by decide⟩
def sourceMap4192 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,7,8,9,10,11,12,13,14,1,2,3,4,5,6] (sourceLabel 8 2 2 v)
def fusedMap4192 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4192_checked : acceptsGraphIso
    (source (graph core4192) (root 8) 2 2) DegreeTwoThreeSpectrum3853.graph sourceMap4192=true := by decide +kernel
theorem fusedMap4192_checked : acceptsGraphIso
    (fused (graph core4192) (root 8) 2 2) DegreeTwoThreeSpectrum3061.graph fusedMap4192=true := by decide +kernel
theorem certified4192 : Certified (graph core4192) (root 8) 2 2 :=
  of_native_maps core4192 DegreeTwoThreeSpectrum3853.graph DegreeTwoThreeSpectrum3061.graph
    sourceMap4192 fusedMap4192 sourceMap4192_checked fusedMap4192_checked
    DegreeTwoThreeFiniteComparisons.comparison4192
#print axioms sourceMap4192_checked
#print axioms fusedMap4192_checked
#print axioms certified4192
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
