/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons98
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4921 : Family 10 := level10.get ⟨1422,by decide⟩
def sourceMap4921 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,8,9,10,11,12,13,14,15,16,7,1,2,3,4,5,6] (sourceLabel 10 2 2 v)
def fusedMap4921 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4921_checked : acceptsGraphIso
    (source (graph core4921) (root 10) 2 2) DegreeTwoThreeSpectrum7522.graph sourceMap4921=true := by decide +kernel
theorem fusedMap4921_checked : acceptsGraphIso
    (fused (graph core4921) (root 10) 2 2) DegreeTwoThreeSpectrum6875.graph fusedMap4921=true := by decide +kernel
theorem certified4921 : Certified (graph core4921) (root 10) 2 2 :=
  of_native_maps core4921 DegreeTwoThreeSpectrum7522.graph DegreeTwoThreeSpectrum6875.graph
    sourceMap4921 fusedMap4921 sourceMap4921_checked fusedMap4921_checked
    DegreeTwoThreeFiniteComparisons.comparison4921
#print axioms sourceMap4921_checked
#print axioms fusedMap4921_checked
#print axioms certified4921
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
