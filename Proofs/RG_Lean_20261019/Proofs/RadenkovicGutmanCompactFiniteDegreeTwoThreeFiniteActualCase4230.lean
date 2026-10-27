/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons84
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4230 : Family 9 := level9.get ⟨153,by decide⟩
def sourceMap4230 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![7,0,1,2,3,4,5,6,15,14,8,9,10,11,12,13] (sourceLabel 9 2 2 v)
def fusedMap4230 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4230_checked : acceptsGraphIso
    (source (graph core4230) (root 9) 2 2) DegreeTwoThreeSpectrum4721.graph sourceMap4230=true := by decide +kernel
theorem fusedMap4230_checked : acceptsGraphIso
    (fused (graph core4230) (root 9) 2 2) DegreeTwoThreeSpectrum3910.graph fusedMap4230=true := by decide +kernel
theorem certified4230 : Certified (graph core4230) (root 9) 2 2 :=
  of_native_maps core4230 DegreeTwoThreeSpectrum4721.graph DegreeTwoThreeSpectrum3910.graph
    sourceMap4230 fusedMap4230 sourceMap4230_checked fusedMap4230_checked
    DegreeTwoThreeFiniteComparisons.comparison4230
#print axioms sourceMap4230_checked
#print axioms fusedMap4230_checked
#print axioms certified4230
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
