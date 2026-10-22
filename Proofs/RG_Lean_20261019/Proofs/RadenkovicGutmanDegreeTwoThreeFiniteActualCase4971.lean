/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons99
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4971 : Family 10 := level10.get ⟨1552,by decide⟩
def sourceMap4971 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4971 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4971_checked : acceptsGraphIso
    (source (graph core4971) (root 10) 2 2) DegreeTwoThreeSpectrum7572.graph sourceMap4971=true := by decide +kernel
theorem fusedMap4971_checked : acceptsGraphIso
    (fused (graph core4971) (root 10) 2 2) DegreeTwoThreeSpectrum6005.graph fusedMap4971=true := by decide +kernel
theorem certified4971 : Certified (graph core4971) (root 10) 2 2 :=
  of_native_maps core4971 DegreeTwoThreeSpectrum7572.graph DegreeTwoThreeSpectrum6005.graph
    sourceMap4971 fusedMap4971 sourceMap4971_checked fusedMap4971_checked
    DegreeTwoThreeFiniteComparisons.comparison4971
#print axioms sourceMap4971_checked
#print axioms fusedMap4971_checked
#print axioms certified4971
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
