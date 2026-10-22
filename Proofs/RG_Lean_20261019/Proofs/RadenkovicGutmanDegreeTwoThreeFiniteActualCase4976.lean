/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons99
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4976 : Family 10 := level10.get ⟨1561,by decide⟩
def sourceMap4976 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,13,14,15,16,7,8,9,10,11,12] (sourceLabel 10 2 2 v)
def fusedMap4976 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4976_checked : acceptsGraphIso
    (source (graph core4976) (root 10) 2 2) DegreeTwoThreeSpectrum7577.graph sourceMap4976=true := by decide +kernel
theorem fusedMap4976_checked : acceptsGraphIso
    (fused (graph core4976) (root 10) 2 2) DegreeTwoThreeSpectrum6025.graph fusedMap4976=true := by decide +kernel
theorem certified4976 : Certified (graph core4976) (root 10) 2 2 :=
  of_native_maps core4976 DegreeTwoThreeSpectrum7577.graph DegreeTwoThreeSpectrum6025.graph
    sourceMap4976 fusedMap4976 sourceMap4976_checked fusedMap4976_checked
    DegreeTwoThreeFiniteComparisons.comparison4976
#print axioms sourceMap4976_checked
#print axioms fusedMap4976_checked
#print axioms certified4976
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
