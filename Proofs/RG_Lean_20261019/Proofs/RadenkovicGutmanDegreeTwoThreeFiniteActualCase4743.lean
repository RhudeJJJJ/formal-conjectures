/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons94
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4743 : Family 10 := level10.get ⟨978,by decide⟩
def sourceMap4743 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,12,13,14,15,16,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 10 2 2 v)
def fusedMap4743 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4743_checked : acceptsGraphIso
    (source (graph core4743) (root 10) 2 2) DegreeTwoThreeSpectrum6973.graph sourceMap4743=true := by decide +kernel
theorem fusedMap4743_checked : acceptsGraphIso
    (fused (graph core4743) (root 10) 2 2) DegreeTwoThreeSpectrum5912.graph fusedMap4743=true := by decide +kernel
theorem certified4743 : Certified (graph core4743) (root 10) 2 2 :=
  of_native_maps core4743 DegreeTwoThreeSpectrum6973.graph DegreeTwoThreeSpectrum5912.graph
    sourceMap4743 fusedMap4743 sourceMap4743_checked fusedMap4743_checked
    DegreeTwoThreeFiniteComparisons.comparison4743
#print axioms sourceMap4743_checked
#print axioms fusedMap4743_checked
#print axioms certified4743
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
