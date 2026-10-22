/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons95
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4787 : Family 10 := level10.get ⟨1100,by decide⟩
def sourceMap4787 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4787 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4787_checked : acceptsGraphIso
    (source (graph core4787) (root 10) 2 2) DegreeTwoThreeSpectrum7180.graph sourceMap4787=true := by decide +kernel
theorem fusedMap4787_checked : acceptsGraphIso
    (fused (graph core4787) (root 10) 2 2) DegreeTwoThreeSpectrum6185.graph fusedMap4787=true := by decide +kernel
theorem certified4787 : Certified (graph core4787) (root 10) 2 2 :=
  of_native_maps core4787 DegreeTwoThreeSpectrum7180.graph DegreeTwoThreeSpectrum6185.graph
    sourceMap4787 fusedMap4787 sourceMap4787_checked fusedMap4787_checked
    DegreeTwoThreeFiniteComparisons.comparison4787
#print axioms sourceMap4787_checked
#print axioms fusedMap4787_checked
#print axioms certified4787
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
