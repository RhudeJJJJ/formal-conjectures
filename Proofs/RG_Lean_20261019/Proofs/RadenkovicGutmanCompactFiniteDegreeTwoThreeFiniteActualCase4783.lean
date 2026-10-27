/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons95
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4783 : Family 10 := level10.get ⟨1086,by decide⟩
def sourceMap4783 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap4783 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4783_checked : acceptsGraphIso
    (source (graph core4783) (root 10) 2 2) DegreeTwoThreeSpectrum7165.graph sourceMap4783=true := by decide +kernel
theorem fusedMap4783_checked : acceptsGraphIso
    (fused (graph core4783) (root 10) 2 2) DegreeTwoThreeSpectrum6155.graph fusedMap4783=true := by decide +kernel
theorem certified4783 : Certified (graph core4783) (root 10) 2 2 :=
  of_native_maps core4783 DegreeTwoThreeSpectrum7165.graph DegreeTwoThreeSpectrum6155.graph
    sourceMap4783 fusedMap4783 sourceMap4783_checked fusedMap4783_checked
    DegreeTwoThreeFiniteComparisons.comparison4783
#print axioms sourceMap4783_checked
#print axioms fusedMap4783_checked
#print axioms certified4783
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
