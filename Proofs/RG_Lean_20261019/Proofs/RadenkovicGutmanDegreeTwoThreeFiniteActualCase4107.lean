/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons82
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4107 : Family 8 := level8.get ⟨50,by decide⟩
def sourceMap4107 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,14,13,7,8,9,10,11,12] (sourceLabel 8 2 2 v)
def fusedMap4107 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4107_checked : acceptsGraphIso
    (source (graph core4107) (root 8) 2 2) DegreeTwoThreeSpectrum3359.graph sourceMap4107=true := by decide +kernel
theorem fusedMap4107_checked : acceptsGraphIso
    (fused (graph core4107) (root 8) 2 2) DegreeTwoThreeSpectrum2336.graph fusedMap4107=true := by decide +kernel
theorem certified4107 : Certified (graph core4107) (root 8) 2 2 :=
  of_native_maps core4107 DegreeTwoThreeSpectrum3359.graph DegreeTwoThreeSpectrum2336.graph
    sourceMap4107 fusedMap4107 sourceMap4107_checked fusedMap4107_checked
    DegreeTwoThreeFiniteComparisons.comparison4107
#print axioms sourceMap4107_checked
#print axioms fusedMap4107_checked
#print axioms certified4107
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
