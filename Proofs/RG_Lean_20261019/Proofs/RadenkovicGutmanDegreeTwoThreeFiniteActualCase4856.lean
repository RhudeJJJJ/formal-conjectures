/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons97
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4856 : Family 10 := level10.get ⟨1266,by decide⟩
def sourceMap4856 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,14,15,16,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap4856 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4856_checked : acceptsGraphIso
    (source (graph core4856) (root 10) 2 2) DegreeTwoThreeSpectrum7348.graph sourceMap4856=true := by decide +kernel
theorem fusedMap4856_checked : acceptsGraphIso
    (fused (graph core4856) (root 10) 2 2) DegreeTwoThreeSpectrum6521.graph fusedMap4856=true := by decide +kernel
theorem certified4856 : Certified (graph core4856) (root 10) 2 2 :=
  of_native_maps core4856 DegreeTwoThreeSpectrum7348.graph DegreeTwoThreeSpectrum6521.graph
    sourceMap4856 fusedMap4856 sourceMap4856_checked fusedMap4856_checked
    DegreeTwoThreeFiniteComparisons.comparison4856
#print axioms sourceMap4856_checked
#print axioms fusedMap4856_checked
#print axioms certified4856
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
