/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons95
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4758 : Family 10 := level10.get ⟨1025,by decide⟩
def sourceMap4758 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4758 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4758_checked : acceptsGraphIso
    (source (graph core4758) (root 10) 2 2) DegreeTwoThreeSpectrum7102.graph sourceMap4758=true := by decide +kernel
theorem fusedMap4758_checked : acceptsGraphIso
    (fused (graph core4758) (root 10) 2 2) DegreeTwoThreeSpectrum6032.graph fusedMap4758=true := by decide +kernel
theorem certified4758 : Certified (graph core4758) (root 10) 2 2 :=
  of_native_maps core4758 DegreeTwoThreeSpectrum7102.graph DegreeTwoThreeSpectrum6032.graph
    sourceMap4758 fusedMap4758 sourceMap4758_checked fusedMap4758_checked
    DegreeTwoThreeFiniteComparisons.comparison4758
#print axioms sourceMap4758_checked
#print axioms fusedMap4758_checked
#print axioms certified4758
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
