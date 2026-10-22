/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons89
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4497 : Family 10 := level10.get ⟨277,by decide⟩
def sourceMap4497 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,6,0,1,2,3,4,5,15,16,14,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap4497 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4497_checked : acceptsGraphIso
    (source (graph core4497) (root 10) 2 2) DegreeTwoThreeSpectrum6459.graph sourceMap4497=true := by decide +kernel
theorem fusedMap4497_checked : acceptsGraphIso
    (fused (graph core4497) (root 10) 2 2) DegreeTwoThreeSpectrum5408.graph fusedMap4497=true := by decide +kernel
theorem certified4497 : Certified (graph core4497) (root 10) 2 2 :=
  of_native_maps core4497 DegreeTwoThreeSpectrum6459.graph DegreeTwoThreeSpectrum5408.graph
    sourceMap4497 fusedMap4497 sourceMap4497_checked fusedMap4497_checked
    DegreeTwoThreeFiniteComparisons.comparison4497
#print axioms sourceMap4497_checked
#print axioms fusedMap4497_checked
#print axioms certified4497
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
