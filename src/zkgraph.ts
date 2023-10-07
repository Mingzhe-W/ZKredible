//@ts-ignore
import { require } from "@hyperoracle/zkgraph-lib";
import { Event, Bytes } from "@hyperoracle/zkgraph-lib";

export function handleEvents(events: Event[]): Bytes {
  let moneyLendTrigger = false;

  // Wait for the verifier to emit a 'verified' event, then trigger the money lending strategy
  if (events.length > 0) {
    moneyLendTrigger = true;
  }

  if (moneyLendTrigger) {
    // if approved, return "yes"
    const approvalMessage = "yes".padEnd(64, '0'); // 64 characters for 32 bytes
    return Bytes.fromHexString(approvalMessage);
  } else {
    // if rejected，return "no"
    const rejectionMessage = "no".padEnd(64, '0'); // 64 characters for 32 bytes
    return Bytes.fromHexString(rejectionMessage);
  }
}