/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons98
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4945 : Family 10 := level10.get ⟨1470,by decide⟩
def sourceMap4945 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,11,12,13,14,15,16,7,8,9,10,1,2,3,4,5,6] (sourceLabel 10 2 2 v)
def fusedMap4945 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4945_checked : acceptsGraphIso
    (source (graph core4945) (root 10) 2 2) DegreeTwoThreeSpectrum7488.graph sourceMap4945=true := by decide +kernel
theorem fusedMap4945_checked : acceptsGraphIso
    (fused (graph core4945) (root 10) 2 2) DegreeTwoThreeSpectrum6953.graph fusedMap4945=true := by decide +kernel
theorem certified4945 : Certified (graph core4945) (root 10) 2 2 :=
  of_native_maps core4945 DegreeTwoThreeSpectrum7488.graph DegreeTwoThreeSpectrum6953.graph
    sourceMap4945 fusedMap4945 sourceMap4945_checked fusedMap4945_checked
    DegreeTwoThreeFiniteComparisons.comparison4945
#print axioms sourceMap4945_checked
#print axioms fusedMap4945_checked
#print axioms certified4945
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
