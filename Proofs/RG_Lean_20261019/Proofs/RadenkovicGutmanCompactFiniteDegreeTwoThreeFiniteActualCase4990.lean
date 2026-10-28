/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons99
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4990 : Family 10 := level10.get ⟨1592,by decide⟩
def sourceMap4990 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap4990 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4990_checked : acceptsGraphIso
    (source (graph core4990) (root 10) 2 2) DegreeTwoThreeSpectrum7591.graph sourceMap4990=true := by decide +kernel
theorem fusedMap4990_checked : acceptsGraphIso
    (fused (graph core4990) (root 10) 2 2) DegreeTwoThreeSpectrum6091.graph fusedMap4990=true := by decide +kernel
theorem certified4990 : Certified (graph core4990) (root 10) 2 2 :=
  of_native_maps core4990 DegreeTwoThreeSpectrum7591.graph DegreeTwoThreeSpectrum6091.graph
    sourceMap4990 fusedMap4990 sourceMap4990_checked fusedMap4990_checked
    DegreeTwoThreeFiniteComparisons.comparison4990
#print axioms sourceMap4990_checked
#print axioms fusedMap4990_checked
#print axioms certified4990
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
