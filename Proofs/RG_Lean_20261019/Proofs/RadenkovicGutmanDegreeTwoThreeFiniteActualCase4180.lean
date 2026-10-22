/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons83
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4180 : Family 8 := level8.get ⟨236,by decide⟩
def sourceMap4180 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap4180 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4180_checked : acceptsGraphIso
    (source (graph core4180) (root 8) 2 2) DegreeTwoThreeSpectrum3832.graph sourceMap4180=true := by decide +kernel
theorem fusedMap4180_checked : acceptsGraphIso
    (fused (graph core4180) (root 8) 2 2) DegreeTwoThreeSpectrum2661.graph fusedMap4180=true := by decide +kernel
theorem certified4180 : Certified (graph core4180) (root 8) 2 2 :=
  of_native_maps core4180 DegreeTwoThreeSpectrum3832.graph DegreeTwoThreeSpectrum2661.graph
    sourceMap4180 fusedMap4180 sourceMap4180_checked fusedMap4180_checked
    DegreeTwoThreeFiniteComparisons.comparison4180
#print axioms sourceMap4180_checked
#print axioms fusedMap4180_checked
#print axioms certified4180
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
