/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons95
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4775 : Family 10 := level10.get ⟨1071,by decide⟩
def sourceMap4775 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4775 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4775_checked : acceptsGraphIso
    (source (graph core4775) (root 10) 2 2) DegreeTwoThreeSpectrum7154.graph sourceMap4775=true := by decide +kernel
theorem fusedMap4775_checked : acceptsGraphIso
    (fused (graph core4775) (root 10) 2 2) DegreeTwoThreeSpectrum6131.graph fusedMap4775=true := by decide +kernel
theorem certified4775 : Certified (graph core4775) (root 10) 2 2 :=
  of_native_maps core4775 DegreeTwoThreeSpectrum7154.graph DegreeTwoThreeSpectrum6131.graph
    sourceMap4775 fusedMap4775 sourceMap4775_checked fusedMap4775_checked
    DegreeTwoThreeFiniteComparisons.comparison4775
#print axioms sourceMap4775_checked
#print axioms fusedMap4775_checked
#print axioms certified4775
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
