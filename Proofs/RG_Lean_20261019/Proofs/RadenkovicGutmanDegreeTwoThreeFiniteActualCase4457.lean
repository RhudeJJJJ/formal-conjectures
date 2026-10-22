/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons89
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4457 : Family 10 := level10.get ⟨135,by decide⟩
def sourceMap4457 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,10,11,12,13,14,15,16,9,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap4457 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4457_checked : acceptsGraphIso
    (source (graph core4457) (root 10) 2 2) DegreeTwoThreeSpectrum6847.graph sourceMap4457=true := by decide +kernel
theorem fusedMap4457_checked : acceptsGraphIso
    (fused (graph core4457) (root 10) 2 2) DegreeTwoThreeSpectrum5065.graph fusedMap4457=true := by decide +kernel
theorem certified4457 : Certified (graph core4457) (root 10) 2 2 :=
  of_native_maps core4457 DegreeTwoThreeSpectrum6847.graph DegreeTwoThreeSpectrum5065.graph
    sourceMap4457 fusedMap4457 sourceMap4457_checked fusedMap4457_checked
    DegreeTwoThreeFiniteComparisons.comparison4457
#print axioms sourceMap4457_checked
#print axioms fusedMap4457_checked
#print axioms certified4457
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
