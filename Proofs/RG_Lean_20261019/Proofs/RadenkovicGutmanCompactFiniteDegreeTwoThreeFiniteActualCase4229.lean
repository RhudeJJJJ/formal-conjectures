/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons84
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4229 : Family 9 := level9.get ⟨150,by decide⟩
def sourceMap4229 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap4229 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4229_checked : acceptsGraphIso
    (source (graph core4229) (root 9) 2 2) DegreeTwoThreeSpectrum4717.graph sourceMap4229=true := by decide +kernel
theorem fusedMap4229_checked : acceptsGraphIso
    (fused (graph core4229) (root 9) 2 2) DegreeTwoThreeSpectrum3906.graph fusedMap4229=true := by decide +kernel
theorem certified4229 : Certified (graph core4229) (root 9) 2 2 :=
  of_native_maps core4229 DegreeTwoThreeSpectrum4717.graph DegreeTwoThreeSpectrum3906.graph
    sourceMap4229 fusedMap4229 sourceMap4229_checked fusedMap4229_checked
    DegreeTwoThreeFiniteComparisons.comparison4229
#print axioms sourceMap4229_checked
#print axioms fusedMap4229_checked
#print axioms certified4229
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
