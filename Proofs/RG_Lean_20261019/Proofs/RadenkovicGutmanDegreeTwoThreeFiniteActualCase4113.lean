/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons82
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4113 : Family 8 := level8.get ⟨68,by decide⟩
def sourceMap4113 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,13,14,7,8,9,10,11,12] (sourceLabel 8 2 2 v)
def fusedMap4113 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4113_checked : acceptsGraphIso
    (source (graph core4113) (root 8) 2 2) DegreeTwoThreeSpectrum3592.graph sourceMap4113=true := by decide +kernel
theorem fusedMap4113_checked : acceptsGraphIso
    (fused (graph core4113) (root 8) 2 2) DegreeTwoThreeSpectrum2371.graph fusedMap4113=true := by decide +kernel
theorem certified4113 : Certified (graph core4113) (root 8) 2 2 :=
  of_native_maps core4113 DegreeTwoThreeSpectrum3592.graph DegreeTwoThreeSpectrum2371.graph
    sourceMap4113 fusedMap4113 sourceMap4113_checked fusedMap4113_checked
    DegreeTwoThreeFiniteComparisons.comparison4113
#print axioms sourceMap4113_checked
#print axioms fusedMap4113_checked
#print axioms certified4113
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
