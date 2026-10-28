/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons97
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4878 : Family 10 := level10.get ⟨1322,by decide⟩
def sourceMap4878 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4878 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4878_checked : acceptsGraphIso
    (source (graph core4878) (root 10) 2 2) DegreeTwoThreeSpectrum7405.graph sourceMap4878=true := by decide +kernel
theorem fusedMap4878_checked : acceptsGraphIso
    (fused (graph core4878) (root 10) 2 2) DegreeTwoThreeSpectrum6632.graph fusedMap4878=true := by decide +kernel
theorem certified4878 : Certified (graph core4878) (root 10) 2 2 :=
  of_native_maps core4878 DegreeTwoThreeSpectrum7405.graph DegreeTwoThreeSpectrum6632.graph
    sourceMap4878 fusedMap4878 sourceMap4878_checked fusedMap4878_checked
    DegreeTwoThreeFiniteComparisons.comparison4878
#print axioms sourceMap4878_checked
#print axioms fusedMap4878_checked
#print axioms certified4878
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
