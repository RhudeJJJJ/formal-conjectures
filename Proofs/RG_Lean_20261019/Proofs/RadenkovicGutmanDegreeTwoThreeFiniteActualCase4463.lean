/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons89
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4463 : Family 10 := level10.get ⟨158,by decide⟩
def sourceMap4463 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,10,11,12,13,14,15,16,9,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap4463 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4463_checked : acceptsGraphIso
    (source (graph core4463) (root 10) 2 2) DegreeTwoThreeSpectrum6855.graph sourceMap4463=true := by decide +kernel
theorem fusedMap4463_checked : acceptsGraphIso
    (fused (graph core4463) (root 10) 2 2) DegreeTwoThreeSpectrum5095.graph fusedMap4463=true := by decide +kernel
theorem certified4463 : Certified (graph core4463) (root 10) 2 2 :=
  of_native_maps core4463 DegreeTwoThreeSpectrum6855.graph DegreeTwoThreeSpectrum5095.graph
    sourceMap4463 fusedMap4463 sourceMap4463_checked fusedMap4463_checked
    DegreeTwoThreeFiniteComparisons.comparison4463
#print axioms sourceMap4463_checked
#print axioms fusedMap4463_checked
#print axioms certified4463
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
